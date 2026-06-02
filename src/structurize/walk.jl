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
    exit_dest::Union{Int, Nothing}   # the loop's primary exit (breaks normally)
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
    # leaves the region. `source` is the block we are leaving — used to resolve
    # an exit block's phis when re-materializing a region-exit.
    advance = (target, source) -> resolve_dest(target, region_blocks, loop_ctx, block, ctx, source)

    while current !== nothing && current ∈ region_blocks
        last_block = current

        # --- Loop header? (only if not already inside this loop) ---
        if loop_ctx === nothing || current != loop_ctx.header
            loop_body = get_loop_at(ctx, current, region_blocks)
            if loop_body !== nothing
                loop_exit = emit_loop!(block, ctx, current, loop_body, region_blocks)
                # Update last_block to the loop's exit predecessor (for merge phi lookup)
                exit_src = current
                if loop_exit !== nothing
                    for b in loop_body
                        loop_exit ∈ ir.cfg.blocks[b].succs && (last_block = b; exit_src = b)
                    end
                end
                current = advance(loop_exit, exit_src)
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
            current = advance(term.label, current)
        elseif term isa GotoIfNot
            next = emit_branch!(block, ctx, current, term, region_blocks, merge_phis, loop_ctx)
            next === nothing && return block
            current = advance(next, current)
        else
            # Fallthrough
            next = current + 1
            current = advance(next <= nblocks ? next : nothing, current)
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
                       ctx::Union{Nothing, StructurizeCtx}=nothing,
                       source::Int=0)
    dest === nothing && return nothing
    if loop_ctx !== nothing && ctx !== nothing &&
       resolve_loop_exit!(block, ctx, dest, source, loop_ctx)
        return nothing
    end
    dest ∈ region_blocks ? dest : nothing
end

"""Resolve a loop boundary on the edge to `dest`, setting `block`'s terminator.
Returns `true` if `dest` is a loop boundary (handled), `false` if it is inside the
loop (a normal forward edge). Two cases — back edge to the header → `ContinueOp`;
any edge leaving the loop → `BreakOp`. The single-exiting latch (`normalize_cf`)
unified every loop to one exit edge, so there is no "primary vs secondary" exit to
distinguish and no re-materialization: an early `return`/`throw` is routed through
the latch into the post-loop dispatch (a multi-exit loop is latched) or *is* the
single exit (then the post-loop walk re-emits it), never dropped to a bare break."""
function resolve_loop_exit!(block::Block, ctx::StructurizeCtx, dest::Int,
                            source::Int, loop_ctx::LoopCtx)
    if dest == loop_ctx.header
        block.terminator === nothing &&
            (block.terminator = ContinueOp(copy(loop_ctx.carried_values)))
        return true
    elseif dest ∉ loop_ctx.loop_blocks
        block.terminator === nothing &&
            (block.terminator = BreakOp(copy(loop_ctx.break_values)))
        return true
    end
    return false
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
        if stmt isa PhiNode
            materialize_single_edge_phi!(block, ctx, si, stmt)
            continue
        end
        (stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode) && continue
        idx = get(remap, si, si)
        stmt = remap_stmt(stmt, remap)
        push!(block, idx, stmt, ir.stmts.type[si], ir.stmts.flag[si])
        idx != si && anchor_line!(ctx, idx, si)
    end
end

"""A phi reached on a single live edge `φ(#p => v)` is a pure copy `phi := v` —
left by the edge multiplexer's dispatch (an entry reached from exactly one
trampoline). The walk skips multi-edge phis (the loop-header and branch-merge
machinery owns those, both ≥2 edges); a single-edge phi is otherwise dropped, so
its downstream uses become "SSA used but not defined". Materialize it as a rename
(`ssa_remap`): every reader resolving SSAs through `ssa_remap` then sees the
source value, with no extra statement to misplace across a loop boundary (a copy
statement snapshotting a loop-carried value miscompiled empty loops to infinite).
Readers that consult the *raw* phi index — `emit_loop!`'s loop-carried init/carry
values — apply `ssa_remap` explicitly."""
function materialize_single_edge_phi!(block::Block, ctx::StructurizeCtx, si::Int, phi::PhiNode)
    count(k -> isassigned(phi.values, k), eachindex(phi.values)) == 1 || return
    haskey(ctx.ssa_remap, si) && return            # already renamed by an enclosing pass
    haskey(block.body, si) && return               # already a definition at this index
    k = findfirst(k -> isassigned(phi.values, k), eachindex(phi.values))
    v = phi.values[k]
    if v isa SSAValue
        ctx.ssa_remap[si] = get(ctx.ssa_remap, v.id, v.id)
    else
        push!(block, si, v, ctx.types[si])         # constant copy (no SSA to track)
        anchor_line!(ctx, si, si)
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

"""True iff the branch at `current` has no continuation edges — both arms
diverge (return/throw/break/continue). The only legitimate reason
`find_branch_regions` returns `merge === nothing` once continuations are
single-entry (post `normalize_cf`)."""
function _both_arms_diverge(ctx::StructurizeCtx, current::Int, true_dest::Int,
                            false_dest::Int, then_blocks::Set{Int}, else_blocks::Set{Int},
                            region_blocks::Set{Int}, loop_ctx::Union{Nothing, LoopCtx})
    entries, _ = branch_continuation(ctx, current, true_dest, false_dest,
                                     then_blocks, else_blocks, region_blocks, loop_ctx)
    return isempty(entries)
end

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

    # Determine branch regions and merge block using dominance + exclusion.
    # A multi-entry continuation (the short-circuit shape `if a||b { body }`,
    # nested gated bodies, N-way merges) is collapsed to a single entry upstream
    # by `normalize_cf`'s continuation multiplexer, so by here the continuation is
    # always single-entry: `merge` is the unique entry, or `nothing` iff both arms
    # diverge (zero continuation edges). The lift therefore has one branch path —
    # no shape-matching (`find_gated_body` is gone; invariant I4).
    then_blocks, else_blocks, merge = find_branch_regions(
        ctx, current, true_dest, false_dest, region_blocks, loop_ctx)
    @assert merge !== nothing || _both_arms_diverge(ctx, current, true_dest, false_dest,
                                                    then_blocks, else_blocks, region_blocks, loop_ctx) """
        multi-entry continuation reached the lift at BB$current — normalize_cf's \
        continuation multiplexer should have collapsed it (internal error)"""

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
    # Continuation-by-exclusion finds the *real* merge directly, so a phi-free
    # merge is genuinely phi-free: the walk continues through it without a
    # separate pass-through "absorption" step (D-absorb retired). A no-phi merge
    # yields `nothing` here → the "merge exists but no phis" path below.
    merge_phis = if merge !== nothing && merge ∈ region_blocks &&
                   (!haskey(ctx.loop_map, merge) || is_multi_entry_header)
        phis = extract_merge_phis(ir, merge, region_blocks)
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
            phi_types = [ctx.types[p.ssa_idx] for p in outer_merge_phis]
            # The IfOp yields the outer-merge values only if at least one arm
            # actually yields (reaches the outer continuation). If BOTH arms
            # diverge (return/break/continue), the IfOp has no results — and this
            # block, reached only through it, is itself unreachable past the IfOp.
            # `getfield`-ing a result-less IfOp can't be lowered (its results
            # vector is empty), so yield `Undef` placeholders instead: the
            # YieldOp is dead (never reached), so the values are never observed.
            if_ssa = alloc_ssa!(ctx)
            anchor_line!(ctx, if_ssa, branch_anchor)
            if then_blk.terminator isa YieldOp || else_blk.terminator isa YieldOp
                push!(block, if_ssa, if_op, Tuple{phi_types...})
                yield_values = IRValue[]
                for (i, phi_type) in enumerate(phi_types)
                    fresh = alloc_ssa!(ctx)
                    push!(block, fresh, Expr(:call, Core.getfield, SSAValue(if_ssa), i), phi_type)
                    anchor_line!(ctx, fresh, branch_anchor)
                    push!(yield_values, SSAValue(fresh))
                end
                block.terminator = YieldOp(yield_values)
            else
                push!(block, if_ssa, if_op, Nothing)
                block.terminator = YieldOp(IRValue[Undef(t) for t in phi_types])
            end
        else
            if_ssa = alloc_ssa!(ctx)
            push!(block, if_ssa, if_op, Nothing)
            anchor_line!(ctx, if_ssa, branch_anchor)
        end
        return nothing
    end
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
    # Loop boundary (continue / break / re-materialized exit path)?
    if loop_ctx !== nothing && resolve_loop_exit!(b, ctx, dest, from, loop_ctx)
        return b
    end
    # Merge phis? Use reachability from dest to find the right phi-edge value and
    # yield it directly. Multi-entry continuations (the short-circuit `&&`/`||`
    # shape, where a value is defined in a block between the arms and the merge)
    # were collapsed to single-entry upstream by `normalize_cf`'s continuation
    # multiplexer, so the value is always visible here — no tail duplication.
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
`&&`/`||`) were collapsed to single-entry upstream by `normalize_cf`, so the
yield value is always visible — no tail duplication.
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
