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
    # Track the dest that caused the walker to step out of `region_blocks`. Used
    # by the exit-yield logic to inline-structurize past the region boundary
    # when the merge phi value is defined past `last_block` (short-circuit
    # `||`-style patterns).
    exit_dest::Union{Nothing, Int} = nothing

    # Advance the walker toward `target`; if that step leaves the region, record
    # the target in `exit_dest` so the exit-yield logic can find the value.
    advance = target -> begin
        nc = resolve_dest(target, region_blocks, loop_ctx, block)
        nc === nothing && target !== nothing && (exit_dest = target)
        nc
    end

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
        set_exit_yield!(block, ir, ctx, merge_phis, last_block, exit_dest, loop_ctx)
    end

    return block
end

"""
Resolve a destination block, checking loop boundaries.
Returns the dest to continue walking, or nothing if it's a loop exit/back-edge.
"""
function resolve_dest(dest, region_blocks::Set{Int},
                       loop_ctx::Union{Nothing, LoopCtx}, block::Block)
    dest === nothing && return nothing
    if loop_ctx !== nothing
        if dest == loop_ctx.header
            block.terminator === nothing &&
                (block.terminator = ContinueOp(copy(loop_ctx.carried_values)))
            return nothing
        elseif dest ∉ loop_ctx.loop_blocks
            block.terminator === nothing &&
                (block.terminator = BreakOp(copy(loop_ctx.break_values)))
            return nothing
        end
    end
    dest ∈ region_blocks ? dest : nothing
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
        push!(block, idx, stmt, ir.stmts.type[si])
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
        # If merge has no phis, check its successors for phis
        # (handles pass-through merge blocks like in || patterns)
        if isempty(phis)
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
            b.terminator = BreakOp(copy(loop_ctx.break_values))
            return b
        end
    end
    # Merge phis? Use reachability from dest to find the right phi edge value.
    if merge_phis !== nothing && !isempty(merge_phis)
        pred = find_exit_predecessor(merge_phis, Set{Int}([dest]), from, ir)
        # If `pred` lies past `dest` (the BFS walked beyond `dest` to find a phi
        # predecessor), the yield value is defined inside `dest`'s subtree and is
        # not visible in the empty block. Inline-structurize that subtree with
        # fresh SSA indices so the value is materialized locally. This handles
        # short-circuit `&&`/`||` patterns where the merge tail is reached from
        # multiple sibling regions.
        #
        # `pred != from` skips duplication when the merge phi has a direct edge
        # from the branch source itself: the empty block IS that edge, so
        # yielding the from-edge value directly is correct.
        if pred != dest && pred != from && dominates(ctx.domtree, dest, pred)
            tail_duplicate_branch!(b, dest, merge_phis, loop_ctx, ir, ctx)
        else
            b.terminator = make_yield_for_edge(ir, merge_phis, pred, b, ctx)
        end
    end
    return b
end

"""
Inline-structurize `dest`'s dominator subtree into `b` with fresh SSA indices.

Used by `make_empty_branch_block` when a branch must yield a value defined in a
block past `dest` (the short-circuit `&&`/`||` pattern, where the merge tail is
shared between sibling regions). The dominator subtree is closed under
predecessors, so we can structurize it as a self-contained region; cloning with
fresh indices avoids violating SSA uniqueness when the same tail also appears
in a sibling branch.
"""
function tail_duplicate_branch!(b::Block, dest::Int,
                                 merge_phis::Vector{MergePhiInfo},
                                 loop_ctx::Union{Nothing, LoopCtx},
                                 ir::IRCode, ctx::StructurizeCtx)
    nblocks = length(ir.cfg.blocks)
    full_region = Set{Int}(1:nblocks)
    subtree = Set{Int}()
    collect_dominated!(subtree, ctx.domtree, dest, full_region)

    saved_remap = copy(ctx.ssa_remap)
    for bb_idx in subtree
        bb = ir.cfg.blocks[bb_idx]
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            (stmt isa GotoNode || stmt isa GotoIfNot ||
             stmt isa ReturnNode) && continue
            haskey(ctx.ssa_remap, si) && continue
            fresh = alloc_ssa!(ctx)
            ctx.ssa_remap[si] = fresh
            anchor_line!(ctx, fresh, si)
        end
    end

    sub_block = structurize_region!(ctx, dest, subtree;
                                     merge_phis=merge_phis,
                                     loop_ctx=loop_ctx)

    ctx.ssa_remap = saved_remap

    for (idx, entry) in sub_block.body
        push!(b.body, (idx, entry.stmt, entry.typ))
    end
    b.terminator = sub_block.terminator
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
Set a region's exit terminator on `blk`. Mirrors `make_empty_branch_block`'s
short-circuit handling: when the resolved phi predecessor lies past
`last_block` and we know the out-of-region successor `exit_dest` that caused
the walker to leave, inline-structurize `exit_dest`'s dominator subtree so the
yield value is materialized locally. Otherwise fall back to a direct
`make_yield_for_edge`.
"""
function set_exit_yield!(blk::Block, ir::IRCode, ctx::StructurizeCtx,
                          merge_phis::Vector{MergePhiInfo}, last_block::Int,
                          exit_dest::Union{Nothing, Int}, loop_ctx::Union{Nothing, LoopCtx})
    pred = find_exit_predecessor(merge_phis, Set{Int}([last_block]), last_block, ir)
    if pred != last_block && exit_dest !== nothing &&
       dominates(ctx.domtree, exit_dest, pred)
        tail_duplicate_branch!(blk, exit_dest, merge_phis, loop_ctx, ir, ctx)
    else
        blk.terminator = make_yield_for_edge(ir, merge_phis, pred, blk, ctx)
    end
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
