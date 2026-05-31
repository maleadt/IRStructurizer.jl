#=============================================================================
 Core Algorithm
=============================================================================#

"""
    MergePhiInfo

Info about a phi node at a merge/exit block. `edge_values` maps predecessor
block index → value on that edge.
"""
struct MergePhiInfo
    ssa_idx::Int
    edge_values::Dict{Int, Any}
end

"""
    LoopCtx

Optional context for structurizing loop bodies. When present, back-edges to
`header` become ContinueOp and edges outside `loop_blocks` become BreakOp.
"""
struct LoopCtx
    header::Int
    loop_blocks::Set{Int}
    carried_values::Vector{IRValue}
    break_values::Vector{IRValue}
end

"""
    structurize_region!(ctx, entry, region_blocks; merge_phis, loop_ctx) -> Block

Recursively structurize a set of basic blocks into a single Block.

- `merge_phis`: if provided, the block's terminator will be YieldOp with merge values.
- `loop_ctx`: if provided, back-edges/exits become ContinueOp/BreakOp.
"""
function structurize_region!(ctx::StructurizeCtx, entry::Int, region_blocks::Set{Int};
                              merge_phis::Union{Nothing, Vector{MergePhiInfo}}=nothing,
                              loop_ctx::Union{Nothing, LoopCtx}=nothing)
    block = Block()
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)
    current = entry
    last_block = entry

    # Advance the walker toward `target`, resolving loop boundaries
    # (back-edge → ContinueOp, exit → BreakOp); returns nothing if `target`
    # leaves the region.
    advance = target -> resolve_dest(target, region_blocks, loop_ctx, block, ctx)

    while current !== nothing && current ∈ region_blocks
        last_block = current

        # --- Loop header? (only if not already inside this loop) ---
        if loop_ctx === nothing || current != loop_ctx.header
            loop_body = get_loop_at(ctx, current, region_blocks)
            if loop_body !== nothing
                loop_exit = emit_loop!(block, ctx, current, loop_body, region_blocks)
                # Update last_block to the loop's exit predecessor (for merge phi lookup)
                if loop_exit !== nothing
                    for b in loop_body
                        loop_exit ∈ ir.cfg.blocks[b].succs && (last_block = b)
                    end
                end
                current = advance(loop_exit)
                continue
            end
        end

        # --- Emit non-phi/non-terminator statements ---
        emit_block_stmts!(block, ctx, current)

        # --- Handle terminator ---
        term = find_terminator(ir, current)

        if term isa ReturnNode
            if !isempty(ctx.ssa_remap) && isdefined(term, :val)
                val = remap_ssa_ref(term.val, ctx.ssa_remap)
                block.terminator = val === term.val ? term : ReturnNode(val)
            else
                block.terminator = term
            end
            return block
        elseif term isa GotoNode
            current = advance(term.label)
        elseif term isa GotoIfNot
            next = emit_branch!(block, ctx, current, term, region_blocks, merge_phis, loop_ctx)
            next === nothing && return block
            current = advance(next)
        else
            # Fallthrough
            next = current + 1
            current = advance(next <= nblocks ? next : nothing)
        end
    end

    # Region ended — set terminator if not already set
    if block.terminator === nothing && merge_phis !== nothing
        set_exit_yield!(block, ir, ctx, merge_phis, last_block)
    end

    return block
end

"""
Resolve a destination block, checking loop boundaries.
Returns the dest to continue walking, or nothing if it's a loop exit/back-edge.
"""
function resolve_dest(dest, region_blocks::Set{Int},
                       loop_ctx::Union{Nothing, LoopCtx}, block::Block,
                       ctx::Union{Nothing, StructurizeCtx}=nothing)
    dest === nothing && return nothing
    if loop_ctx !== nothing
        if dest == loop_ctx.header
            block.terminator === nothing &&
                (block.terminator = ContinueOp(copy(loop_ctx.carried_values)))
            return nothing
        elseif dest ∉ loop_ctx.loop_blocks
            # A loop-exit edge to a dead-end throw/unreachable block (no successors,
            # terminal type Union{}) is NOT a normal break: collapsing it to a
            # BreakOp would discard the throw. Emit the block's statements in place
            # and terminate with `unreachable` (`ReturnNode()`), matching the
            # non-loop throw path (which keeps the throw call ::Union{}).
            if ctx !== nothing && block.terminator === nothing &&
               is_throw_exit(ctx.ir, dest)
                emit_throw_exit!(block, ctx, dest)
                return nothing
            end
            block.terminator === nothing &&
                (block.terminator = BreakOp(copy(loop_ctx.break_values)))
            return nothing
        end
    end
    dest ∈ region_blocks ? dest : nothing
end

"""A dead-end throw/unreachable block: no successors and terminal type `Union{}`."""
function is_throw_exit(ir::IRCode, dest::Int)
    1 <= dest <= length(ir.cfg.blocks) || return false
    bb = ir.cfg.blocks[dest]
    isempty(bb.succs) || return false
    return ir.stmts.type[last(bb.stmts)] === Union{}
end

"""Emit a dead-end throw block's statements into `block` and set the `unreachable`
(`ReturnNode()`) terminator — keeps the throw call instead of dropping it as a break."""
function emit_throw_exit!(block::Block, ctx::StructurizeCtx, dest::Int)
    emit_block_stmts!(block, ctx, dest)
    block.terminator = ReturnNode()  # unreachable
    return block
end

#=============================================================================
 Statement Emission
=============================================================================#

function emit_block_stmts!(block::Block, ctx::StructurizeCtx, bb_idx::Int)
    ir = ctx.ir
    remap = ctx.ssa_remap
    bb = ir.cfg.blocks[bb_idx]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        (stmt isa PhiNode || stmt isa GotoNode ||
         stmt isa GotoIfNot || stmt isa ReturnNode) && continue
        idx = get(remap, si, si)
        stmt = remap_stmt(stmt, remap)
        push!(block, idx, stmt, ir.stmts.type[si], ir.stmts.flag[si])
        idx != si && anchor_line!(ctx, idx, si)
    end
end

function find_terminator(ir::IRCode, bb_idx::Int)
    bb = ir.cfg.blocks[bb_idx]
    for si in first(bb.stmts):last(bb.stmts)
        s = ir.stmts.stmt[si]
        (s isa GotoIfNot || s isa GotoNode || s isa ReturnNode) && return s
    end
    return nothing  # fallthrough
end

#=============================================================================
 Branch Lifting (IfOp)
=============================================================================#

"""
    emit_branch!(block, ctx, current, gotoifnot, region_blocks, outer_merge_phis) -> next

Create an IfOp for a conditional branch. Returns the merge block index to
continue with, or nothing if both branches exit/diverge.
"""
function emit_branch!(block::Block, ctx::StructurizeCtx, current::Int,
                      gotoifnot::GotoIfNot, region_blocks::Set{Int},
                      outer_merge_phis::Union{Nothing, Vector{MergePhiInfo}},
                      loop_ctx::Union{Nothing, LoopCtx}=nothing)
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)

    # GotoIfNot: cond=false → dest, cond=true → fallthrough
    false_dest = gotoifnot.dest
    # Derive fallthrough from CFG successors (not current+1, which assumes sequential layout)
    bb_succs = ir.cfg.blocks[current].succs
    true_dest = length(bb_succs) == 1 ? only(bb_succs) :
                first(s for s in bb_succs if s != false_dest)
    cond = remap_ssa_ref(gotoifnot.cond, ctx.ssa_remap)

    # Determine branch regions and merge block using dominance
    then_blocks, else_blocks, merge = find_branch_regions(
        ctx, current, true_dest, false_dest, region_blocks)

    # Short-circuit-guarded body (`if a || b { body }`, `a && b`, value forms):
    # the body is the multi-entry continuation reached from BOTH arms, so it falls
    # into neither then/else region. Materialize the combined predicate as a
    # boolean region selector and emit the body ONCE under `scf.if` — MLIR's
    # transformCFGToSCF edge multiplexer, no body duplication.
    gated = find_gated_body(ctx, current, true_dest, false_dest,
                            then_blocks, else_blocks, region_blocks, loop_ctx)
    if gated !== nothing
        body_entry, body_region, gate_merge = gated
        return emit_gated_branch!(block, ctx, current, cond, true_dest, false_dest,
                                  then_blocks, else_blocks, body_entry, body_region,
                                  gate_merge, region_blocks, loop_ctx)
    end

    # If merge exists and is in region, extract its phis.
    # Skip phis at loop headers — UNLESS the header has multiple non-loop predecessors
    # (entry multiplexer case: branch must yield the correct entry values).
    # Only extract multi-entry header phis OUTSIDE the loop (for the entry IfOp).
    # Inside the loop, the header is reached via the latch (single back-edge) → ContinueOp.
    is_multi_entry_header = if merge !== nothing && haskey(ctx.loop_map, merge) &&
                               loop_ctx === nothing  # not inside a loop
        loop_body = ctx.loop_map[merge]
        count(p -> p ∉ loop_body, ir.cfg.blocks[merge].preds) > 1
    else
        false
    end
    merge_phis = if merge !== nothing && merge ∈ region_blocks &&
                   (!haskey(ctx.loop_map, merge) || is_multi_entry_header)
        phis = extract_merge_phis(ir, merge, region_blocks)
        # No phis: absorb a genuine pass-through (no-phi block forwarding
        # unconditionally) and use its successor's phis — the || pattern. Gate on
        # a single successor: a multi-successor merge is itself a branch (e.g. a
        # sequential `if` sharing the condition) and must not be absorbed.
        if isempty(phis) && length(ir.cfg.blocks[merge].succs) == 1
            for succ in ir.cfg.blocks[merge].succs
                if succ ∈ region_blocks && !haskey(ctx.loop_map, succ)
                    succ_phis = extract_merge_phis(ir, succ, region_blocks)
                    if !isempty(succ_phis)
                        # Absorb the pass-through block into the branch regions
                        # and use the successor as the real merge
                        merge = succ
                        phis = succ_phis
                        break
                    end
                end
            end
        end
        isempty(phis) ? nothing : phis
    else
        nothing
    end

    # Determine what to pass as exit phis to sub-regions
    # If both branches exit our region, they need to yield outer_merge_phis
    sub_merge_phis = if merge !== nothing && merge ∈ region_blocks
        merge_phis  # yield inner merge phis
    else
        outer_merge_phis  # propagate outer merge phis
    end

    # Build then/else blocks recursively (propagate loop_ctx for break/continue)
    then_blk = if !isempty(then_blocks)
        structurize_region!(ctx, true_dest, then_blocks;
                             merge_phis=sub_merge_phis, loop_ctx=loop_ctx)
    else
        make_empty_branch_block(true_dest, current, sub_merge_phis, loop_ctx, ir, ctx)
    end

    else_blk = if !isempty(else_blocks)
        structurize_region!(ctx, false_dest, else_blocks;
                             merge_phis=sub_merge_phis, loop_ctx=loop_ctx)
    else
        make_empty_branch_block(false_dest, current, sub_merge_phis, loop_ctx, ir, ctx)
    end

    # Anchor for debug info: use the branch terminator's location
    branch_anchor = last(ir.cfg.blocks[current].stmts)

    if merge !== nothing && merge ∈ region_blocks && merge_phis !== nothing
        # --- Inner merge exists: standard IfOp ---
        set_branch_yields!(then_blk, merge_phis, then_blocks, current, ir, block, ctx)
        set_branch_yields!(else_blk, merge_phis, else_blocks, current, ir, block, ctx)

        if_op = IfOp(cond, then_blk, else_blk)
        phi_indices = [p.ssa_idx for p in merge_phis]
        phi_types = [ctx.types[p.ssa_idx] for p in merge_phis]
        emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx, branch_anchor)
        return merge
    elseif merge !== nothing && merge ∈ region_blocks
        # Merge exists but no phis
        set_yield_if_needed!(then_blk)
        set_yield_if_needed!(else_blk)
        if_op = IfOp(cond, then_blk, else_blk)
        if_ssa = alloc_ssa!(ctx)
        push!(block, if_ssa, if_op, Tuple{})
        anchor_line!(ctx, if_ssa, branch_anchor)
        # If merge is the loop header, both branches already handle the loop flow
        # (break/continue inside). Don't continue walking at the header.
        if loop_ctx !== nothing && merge == loop_ctx.header
            return nothing
        end
        return merge
    else
        # --- Both branches exit/diverge ---
        # sub_merge_phis was already passed to recursive calls, so YieldOps are set
        set_yield_if_needed!(then_blk)
        set_yield_if_needed!(else_blk)

        if_op = IfOp(cond, then_blk, else_blk)

        if outer_merge_phis !== nothing && !isempty(outer_merge_phis)
            # Use fresh indices for getfields — these are intermediate values
            # fed to YieldOp, not final definitions. The outermost emit_ifop_result!
            # (in the merge case) keeps the original phi indices.
            phi_types = [ctx.types[p.ssa_idx] for p in outer_merge_phis]
            if_ssa = alloc_ssa!(ctx)
            result_type = Tuple{phi_types...}
            push!(block, if_ssa, if_op, result_type)
            anchor_line!(ctx, if_ssa, branch_anchor)
            yield_values = IRValue[]
            for (i, phi_type) in enumerate(phi_types)
                fresh = alloc_ssa!(ctx)
                push!(block, fresh, Expr(:call, Core.getfield, SSAValue(if_ssa), i), phi_type)
                anchor_line!(ctx, fresh, branch_anchor)
                push!(yield_values, SSAValue(fresh))
            end
            block.terminator = YieldOp(yield_values)
        else
            if_ssa = alloc_ssa!(ctx)
            push!(block, if_ssa, if_op, Nothing)
            anchor_line!(ctx, if_ssa, branch_anchor)
        end
        return nothing
    end
end

"""
    emit_gated_branch!(...) -> next

Emit a short-circuit-guarded body (`if a || b { body }; rest`) as MLIR's
`transformCFGToSCF` edge multiplexer — the body is structured ONCE, never
duplicated.

The continuation has two entry blocks (`body`, `rest=merge`). The multiplexer
specializes to:

1. An entry `IfOp(cond)` that materializes a boolean region selector — the
   combined predicate `a || b` — as block result `disc`. Reusing the merge-phi
   machinery this is a synthetic phi `disc = φ(reaches-body => true, reaches-rest
   => false)`; the recursive walk routes each arm leaf to the right constant, so
   nested branches (`a || b || c`) become nested IfOps yielding `disc`. When the
   continuation carries values (a value-producing `||`/`&&`), the multiplexer
   also yields, per merge phi, the value on the skip-body (arm→merge) edges as
   additional block results.
2. A single `scf.if disc { body } { skip }` that runs the body ONCE. Its results
   are the merge phi values: the body arm yields the body→merge values; the skip
   arm forwards the values the entry IfOp produced for the skip path.
3. The walk continues at `merge`, where the original phi SSAs are now defined by
   the gated IfOp's results.
"""
# MLIR edge multiplexer for a short-circuit-guarded body (CFGToSCF.cpp
# `EdgeMultiplexer`: https://github.com/llvm/llvm-project/blob/cabad14763b27802296b44b3b5e507f6a4f7a3c5/mlir/lib/Transforms/Utils/CFGToSCF.cpp):
# the entry IfOp yields a boolean selector (the combined predicate) + skip-path
# merge values, then one `scf.if selector { body }` runs the body once.
function emit_gated_branch!(block::Block, ctx::StructurizeCtx, current::Int,
                            cond, true_dest::Int, false_dest::Int,
                            then_blocks::Set{Int}, else_blocks::Set{Int},
                            body_entry::Int, body_region::Set{Int},
                            merge::Int, region_blocks::Set{Int},
                            loop_ctx::Union{Nothing, LoopCtx})
    ir = ctx.ir
    branch_anchor = last(ir.cfg.blocks[current].stmts)

    # merge phis (only if `merge` is in this region; an outer-merge nested body
    # has no escaping value). skip_preds = arm→merge edges (not in the body).
    mp = merge ∈ region_blocks ? extract_merge_phis(ir, merge, region_blocks) : MergePhiInfo[]
    skip_preds = Int[p for p in ir.cfg.blocks[merge].preds if p ∉ body_region]

    # --- 1. Entry IfOp: yield the selector + skip-path values ---
    # Selector phi: true on body-reaching arms, false on skip arms; skip phis
    # forward each merge phi's skip-edge value (Undef on the body edge).
    disc_ssa = alloc_ssa!(ctx)
    set_ssa_type!(ctx, disc_ssa, Bool)
    disc_ev = Dict{Int,Any}(body_entry => true)
    for p in skip_preds; disc_ev[p] = false; end
    disc_phis = MergePhiInfo[MergePhiInfo(disc_ssa, disc_ev)]

    skip_ssas = Int[]   # entry-IfOp result holding each phi's skip-path value
    for phi in mp
        s = alloc_ssa!(ctx)
        set_ssa_type!(ctx, s, ctx.types[phi.ssa_idx])
        push!(skip_ssas, s)
        ev = Dict{Int,Any}(body_entry => Undef(ctx.types[phi.ssa_idx]))
        for p in skip_preds
            ev[p] = get(phi.edge_values, p, Undef(ctx.types[phi.ssa_idx]))
        end
        push!(disc_phis, MergePhiInfo(s, ev))
    end

    then_blk = if !isempty(then_blocks)
        structurize_region!(ctx, true_dest, then_blocks; merge_phis=disc_phis, loop_ctx=loop_ctx)
    else
        make_empty_branch_block(true_dest, current, disc_phis, loop_ctx, ir, ctx)
    end
    else_blk = if !isempty(else_blocks)
        structurize_region!(ctx, false_dest, else_blocks; merge_phis=disc_phis, loop_ctx=loop_ctx)
    else
        make_empty_branch_block(false_dest, current, disc_phis, loop_ctx, ir, ctx)
    end
    set_branch_yields!(then_blk, disc_phis, then_blocks, current, ir, block, ctx)
    set_branch_yields!(else_blk, disc_phis, else_blocks, current, ir, block, ctx)

    disc_if = IfOp(cond, then_blk, else_blk)
    disc_indices = Int[p.ssa_idx for p in disc_phis]
    disc_types = Any[ctx.types[i] for i in disc_indices]
    emit_ifop_result!(block, disc_if, disc_indices, disc_types, ctx, branch_anchor)

    # --- 2. Structurize the body ONCE, yielding its merge-phi contributions ---
    body_merge_phis = isempty(mp) ? nothing : mp
    body_blk = structurize_region!(ctx, body_entry, body_region;
                                   merge_phis=body_merge_phis, loop_ctx=loop_ctx)
    set_yield_if_needed!(body_blk)

    # --- 3. Gate it: scf.if disc { body } { forward skip values } ---
    skip_blk = Block()
    skip_blk.terminator = YieldOp(IRValue[SSAValue(s) for s in skip_ssas])
    body_if = IfOp(SSAValue(disc_ssa), body_blk, skip_blk)
    if isempty(mp)
        if_ssa = alloc_ssa!(ctx)
        push!(block, if_ssa, body_if, Tuple{})
        anchor_line!(ctx, if_ssa, branch_anchor)
    else
        phi_indices = Int[p.ssa_idx for p in mp]
        phi_types = Any[ctx.types[p.ssa_idx] for p in mp]
        emit_ifop_result!(block, body_if, phi_indices, phi_types, ctx, branch_anchor)
    end

    # --- 4. Continue at merge ---
    return merge
end

"""Set yield terminator on a branch block for merge phis, if not already set."""
function set_branch_yields!(blk::Block, merge_phis::Vector{MergePhiInfo},
                            branch_blocks::Set{Int}, branch_entry::Int,
                            ir::IRCode, parent_block::Block, ctx::StructurizeCtx)
    blk.terminator !== nothing && return  # already set (e.g., ReturnNode, inner yield)

    # Find the exit block: the block in branch_blocks (or branch_entry if empty)
    # that has an edge to a merge phi predecessor
    exit_block = find_exit_predecessor(merge_phis, branch_blocks, branch_entry, ir)
    blk.terminator = make_yield_for_edge(ir, merge_phis, exit_block, blk, ctx)
end

function set_yield_if_needed!(blk::Block)
    blk.terminator === nothing && (blk.terminator = YieldOp())
end

"""Create an empty branch block with appropriate terminator for its destination."""
function make_empty_branch_block(dest::Int, from::Int,
                                  merge_phis::Union{Nothing, Vector{MergePhiInfo}},
                                  loop_ctx::Union{Nothing, LoopCtx},
                                  ir::IRCode, ctx::StructurizeCtx)
    b = Block()
    # Loop boundary?
    if loop_ctx !== nothing
        if dest == loop_ctx.header
            b.terminator = ContinueOp(copy(loop_ctx.carried_values))
            return b
        elseif dest ∉ loop_ctx.loop_blocks
            # Dead-end throw/unreachable exit: emit its statements + `unreachable`
            # instead of collapsing to a BreakOp (which would drop the throw).
            if is_throw_exit(ir, dest)
                emit_throw_exit!(b, ctx, dest)
                return b
            end
            b.terminator = BreakOp(copy(loop_ctx.break_values))
            return b
        end
    end
    # Merge phis? Use reachability from dest to find the right phi-edge value and
    # yield it directly. Multi-entry continuations (the short-circuit `&&`/`||`
    # shape, where a value is defined in a block between the arms and the merge)
    # are handled upstream by the `emit_gated_branch!` edge multiplexer, so the
    # value is always visible here — no tail duplication needed.
    if merge_phis !== nothing && !isempty(merge_phis)
        pred = find_exit_predecessor(merge_phis, Set{Int}([dest]), from, ir)
        b.terminator = make_yield_for_edge(ir, merge_phis, pred, b, ctx)
    end
    return b
end

"""
    find_exit_predecessor(merge_phis, blocks, fallback, ir)

Find the block whose edge to the merge carries the phi value for this branch.
Uses BFS from the branch region through successors (DREAM's reachability
principle: the value a branch contributes to a merge phi is determined by
which phi edge predecessor is reachable from that branch).
"""
function find_exit_predecessor(merge_phis::Vector{MergePhiInfo}, blocks::Set{Int},
                                fallback::Int, ir::IRCode)
    nblocks = length(ir.cfg.blocks)
    seeds = isempty(blocks) ? Set{Int}([fallback]) : blocks

    # Check seeds and fallback directly (before BFS)
    for b in seeds, phi in merge_phis
        haskey(phi.edge_values, b) && return b
    end
    for phi in merge_phis
        haskey(phi.edge_values, fallback) && return fallback
    end

    # BFS through successors of seeds (handles pass-through blocks)
    visited = copy(seeds)
    push!(visited, fallback)  # don't re-enter the branch source
    queue = Int[]
    for b in seeds
        1 <= b <= nblocks || continue
        for succ in ir.cfg.blocks[b].succs
            succ ∈ visited || push!(queue, succ)
        end
    end

    while !isempty(queue)
        b = popfirst!(queue)
        b ∈ visited && continue
        push!(visited, b)

        for phi in merge_phis
            haskey(phi.edge_values, b) && return b
        end

        1 <= b <= nblocks || continue
        for succ in ir.cfg.blocks[b].succs
            succ ∈ visited || push!(queue, succ)
        end
    end

    return fallback
end

"""Create a YieldOp with values from merge phis for a given predecessor edge."""
function make_yield_for_edge(ir::IRCode, merge_phis::Vector{MergePhiInfo},
                              pred::Int, blk::Block, ctx::StructurizeCtx)
    yield_values = IRValue[]
    remap = ctx.ssa_remap
    for phi in merge_phis
        val = get(phi.edge_values, pred, nothing)
        if val !== nothing
            val = remap_ssa_ref(val, remap)
            resolved = resolve_yield_value(blk, phi.ssa_idx, val, remap)
            push!(yield_values, resolved)
        else
            push!(yield_values, Undef(ctx.types[phi.ssa_idx]))
        end
    end
    return YieldOp(yield_values)
end

"""
Set a region's exit terminator on `blk`: resolve which phi-edge predecessor this
region reaches and yield that value. Multi-entry continuations (short-circuit
`&&`/`||`) are handled upstream by the `emit_gated_branch!` edge multiplexer, so
the yield value is always visible — no tail duplication.
"""
function set_exit_yield!(blk::Block, ir::IRCode, ctx::StructurizeCtx,
                          merge_phis::Vector{MergePhiInfo}, last_block::Int)
    pred = find_exit_predecessor(merge_phis, Set{Int}([last_block]), last_block, ir)
    blk.terminator = make_yield_for_edge(ir, merge_phis, pred, blk, ctx)
    return blk.terminator
end

"""
If the block already defines `phi_ssa_idx` (or its remapped index), yield that SSAValue.
Otherwise yield `default_val`.
"""
function resolve_yield_value(blk::Block, phi_ssa_idx::Int, default_val,
                              remap::Dict{Int, Int}=Dict{Int,Int}())
    idx = get(remap, phi_ssa_idx, phi_ssa_idx)
    haskey(blk.body, idx) ? SSAValue(idx) : default_val
end
