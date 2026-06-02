#=============================================================================
 Core Algorithm — the lift, reading the explicit-edge `MBlock` form directly.

 Block arguments + per-edge operands replace Julia phi nodes (the MLIR model), so
 "what value does predecessor P contribute to block B's k-th argument" is just the
 operand on edge P→B (`edge_operands`) — no phi-node scanning, no dense round-trip.
=============================================================================#

"""
    MergePhiInfo

Info about one block argument at a merge/exit block. `ssa_idx` is the argument's
stable id; `edge_values` maps predecessor block index → the operand that edge
contributes to this argument. Built from the `MBlock` args + per-edge operands by
[`extract_merge_phis`](@ref) — the lift then reasons in the same predecessor-keyed
terms whether the value came from a Julia phi or an MLIR-style block argument.
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

"""The operands edge `src`→`dst` carries (parallel to `dst`'s block arguments), or
`nothing` if `src` has no edge to `dst`. A degenerate `GotoIfNot` whose two edges
target the same block is split away by [`split_duplicate_edges!`](@ref) before the
lift, so each predecessor reaches a block by at most one edge here."""
function edge_operands(m, src::Int, dst::Int)
    t = m.blocks[src].term
    if t isa MGoto
        t.edge.target == dst && return t.edge.args
    elseif t isa MCondBr
        t.t.target == dst && return t.t.args
        t.f.target == dst && return t.f.args
    end
    return nothing
end

"""The stable id of a block's last / first body statement (0 if the body is
empty), used as a debug-info anchor for synthesized ops — the branch condition
(last body stmt) for an IfOp, the header's first stmt for a loop."""
last_body_id(ctx::StructurizeCtx, b::Int) =
    (body = (ctx.m::MCFG).blocks[b].body; isempty(body) ? 0 : last(body).id)
first_body_id(ctx::StructurizeCtx, b::Int) =
    (body = (ctx.m::MCFG).blocks[b].body; isempty(body) ? 0 : first(body).id)

"""
    structurize_region!(ctx, entry, region_blocks; merge_phis, loop_ctx) -> Block

Recursively structurize a set of blocks into a single Block.

- `merge_phis`: if provided, the block's terminator will be YieldOp with merge values.
- `loop_ctx`: if provided, back-edges/exits become ContinueOp/BreakOp.
"""
function structurize_region!(ctx::StructurizeCtx, entry::Int, region_blocks::Set{Int};
                              merge_phis::Union{Nothing, Vector{MergePhiInfo}}=nothing,
                              loop_ctx::Union{Nothing, LoopCtx}=nothing)
    block = Block()
    m = ctx.m::MCFG
    current = entry
    last_block = entry

    # Advance the walker toward `target`, resolving loop boundaries
    # (back-edge → ContinueOp, exit → BreakOp); returns nothing if `target`
    # leaves the region.
    advance = target -> resolve_dest(target, region_blocks, loop_ctx, block, ctx)

    while current !== nothing && current ∈ region_blocks
        last_block = current

        # A block argument with a single predecessor is a "phi with one edge" — a
        # pure copy left by an edge multiplexer's dispatch. Rename it to that
        # edge's operand (the MBlock equivalent of materialize_single_edge_phi!);
        # header / merge args (≥2 preds) are owned by the loop / branch machinery
        # and left untouched here.
        bind_single_pred_args!(block, ctx, current)

        # --- Loop header? (only if not already inside this loop) ---
        if loop_ctx === nothing || current != loop_ctx.header
            loop_body = get_loop_at(ctx, current, region_blocks)
            if loop_body !== nothing
                loop_exit = emit_loop!(block, ctx, current, loop_body, region_blocks)
                # Update last_block to the loop's exit predecessor (for merge phi lookup)
                if loop_exit !== nothing
                    for b in loop_body
                        loop_exit ∈ ctx.cfg.blocks[b].succs && (last_block = b)
                    end
                end
                current = advance(loop_exit)
                continue
            end
        end

        # --- Emit body statements (block args are not statements) ---
        emit_block_stmts!(block, ctx, current)

        # --- Handle terminator ---
        term = m.blocks[current].term
        if term isa MReturn
            block.terminator = make_return(ctx, term)
            return block
        elseif term isa MGoto
            current = advance(term.edge.target)
        else  # MCondBr
            next = emit_branch!(block, ctx, current, term::MCondBr, region_blocks, merge_phis, loop_ctx)
            next === nothing && return block
            current = advance(next)
        end
    end

    # Region ended — set terminator if not already set
    if block.terminator === nothing && merge_phis !== nothing
        set_exit_yield!(block, ctx, merge_phis, last_block)
    end

    return block
end

"""Reconstruct the SCI return terminator from an `MReturn` (a value return, a bare
`return`, or an unreachable dead-end)."""
make_return(ctx::StructurizeCtx, t::MReturn) =
    t.has_val ? ReturnNode(remap_ssa_ref(t.val, ctx.ssa_remap)) : ReturnNode()

"""
Resolve a destination block, checking loop boundaries.
Returns the dest to continue walking, or nothing if it's a loop exit/back-edge.
"""
function resolve_dest(dest, region_blocks::Set{Int},
                       loop_ctx::Union{Nothing, LoopCtx}, block::Block,
                       ctx::Union{Nothing, StructurizeCtx}=nothing)
    dest === nothing && return nothing
    if loop_ctx !== nothing && ctx !== nothing &&
       resolve_loop_exit!(block, ctx, dest, loop_ctx)
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
                            loop_ctx::LoopCtx)
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

function emit_block_stmts!(block::Block, ctx::StructurizeCtx, b::Int)
    m = ctx.m::MCFG
    remap = ctx.ssa_remap
    for s in m.blocks[b].body
        idx = get(remap, s.id, s.id)
        stmt = remap_stmt(s.stmt, remap)
        push!(block, idx, stmt, s.type, s.flag)
        idx != s.id && anchor_line!(ctx, idx, s.id)
    end
end

"""Bind the single-predecessor block arguments of `b`. A block argument fed by
exactly one predecessor edge is a pure copy (`arg := that edge's operand`) — left
by an edge multiplexer's dispatch (an entry reached from one dispatch arm). An
SSA-valued operand becomes a rename (`ssa_remap`); a constant/argument/undef
operand is materialized as a copy at the arg's id. Multi-predecessor args (loop
headers, branch merges) carry ≥2 distinct edge operands and are resolved by the
loop / branch machinery instead, so they are skipped here."""
function bind_single_pred_args!(block::Block, ctx::StructurizeCtx, b::Int)
    m = ctx.m::MCFG
    args = m.blocks[b].args
    isempty(args) && return
    preds = ctx.cfg.blocks[b].preds
    length(preds) == 1 || return
    ops = edge_operands(m, only(preds), b)
    ops === nothing && return
    for (k, arg) in enumerate(args)
        haskey(ctx.ssa_remap, arg) && continue   # already renamed by an enclosing pass
        haskey(block.body, arg) && continue       # already a definition at this id
        v = ops[k]
        if v isa SSAValue
            ctx.ssa_remap[arg] = get(ctx.ssa_remap, v.id, v.id)
        else
            push!(block, arg, v, get(ctx.types, arg, Any))   # constant / argument / undef copy
            anchor_line!(ctx, arg, arg)
        end
    end
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
    entries, _ = branch_continuation(ctx.cfg, ctx.domtree, current, true_dest, false_dest,
                                     then_blocks, else_blocks, region_blocks, loop_ctx)
    return isempty(entries)
end

"""
    emit_branch!(block, ctx, current, condbr, region_blocks, outer_merge_phis) -> next

Create an IfOp for a conditional branch. Returns the merge block index to
continue with, or nothing if both branches exit/diverge.
"""
function emit_branch!(block::Block, ctx::StructurizeCtx, current::Int,
                      condbr::MCondBr, region_blocks::Set{Int},
                      outer_merge_phis::Union{Nothing, Vector{MergePhiInfo}},
                      loop_ctx::Union{Nothing, LoopCtx}=nothing)
    # MCondBr carries explicit true/false edges (no fallthrough/succ derivation).
    true_dest = condbr.t.target
    false_dest = condbr.f.target
    cond = remap_ssa_ref(condbr.cond, ctx.ssa_remap)

    # Determine branch regions and merge block using dominance + exclusion.
    # A multi-entry continuation (the short-circuit shape `if a||b { body }`,
    # nested gated bodies, N-way merges) is collapsed to a single entry upstream
    # by `normalize_cf`'s continuation multiplexer, so by here the continuation is
    # always single-entry: `merge` is the unique entry, or `nothing` iff both arms
    # diverge (zero continuation edges). The lift therefore has one branch path —
    # no shape-matching (`find_gated_body` is gone; invariant I4).
    then_blocks, else_blocks, merge = find_branch_regions(
        ctx.cfg, ctx.domtree, current, true_dest, false_dest, region_blocks, loop_ctx)
    @assert merge !== nothing || _both_arms_diverge(ctx, current, true_dest, false_dest,
                                                    then_blocks, else_blocks, region_blocks, loop_ctx) """
        multi-entry continuation reached the lift at BB$current — normalize_cf's \
        continuation multiplexer should have collapsed it (internal error)"""

    # If merge exists and is in region, extract its block args (the "phis").
    # Skip args at loop headers — UNLESS the header has multiple non-loop predecessors
    # (entry multiplexer case: the branch must yield the correct entry values).
    is_multi_entry_header = if merge !== nothing && haskey(ctx.loop_map, merge) &&
                               loop_ctx === nothing  # not inside a loop
        loop_body = ctx.loop_map[merge]
        count(p -> p ∉ loop_body, ctx.cfg.blocks[merge].preds) > 1
    else
        false
    end
    # Continuation-by-exclusion finds the *real* merge directly, so a no-arg merge
    # is genuinely arg-free: the walk continues through it without a separate
    # pass-through step. A no-arg merge yields `nothing` here.
    merge_phis = if merge !== nothing && merge ∈ region_blocks &&
                   (!haskey(ctx.loop_map, merge) || is_multi_entry_header)
        phis = extract_merge_phis(ctx, merge, region_blocks)
        isempty(phis) ? nothing : phis
    else
        nothing
    end

    # What to pass as exit phis to sub-regions: if both branches exit our region,
    # they need to yield outer_merge_phis.
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
        make_empty_branch_block(ctx, true_dest, current, sub_merge_phis, loop_ctx)
    end

    else_blk = if !isempty(else_blocks)
        structurize_region!(ctx, false_dest, else_blocks;
                             merge_phis=sub_merge_phis, loop_ctx=loop_ctx)
    else
        make_empty_branch_block(ctx, false_dest, current, sub_merge_phis, loop_ctx)
    end

    # Anchor for debug info: the branch condition (the block's last body stmt).
    branch_anchor = last_body_id(ctx, current)

    if merge !== nothing && merge ∈ region_blocks && merge_phis !== nothing
        # --- Inner merge exists: standard IfOp ---
        set_branch_yields!(then_blk, merge_phis, then_blocks, current, ctx)
        set_branch_yields!(else_blk, merge_phis, else_blocks, current, ctx)

        if_op = IfOp(cond, then_blk, else_blk)
        phi_indices = [p.ssa_idx for p in merge_phis]
        phi_types = [ctx.types[p.ssa_idx] for p in merge_phis]
        emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx, branch_anchor)
        return merge
    elseif merge !== nothing && merge ∈ region_blocks
        # Merge exists but no args
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
                            ctx::StructurizeCtx)
    blk.terminator !== nothing && return  # already set (e.g., ReturnNode, inner yield)

    # Find the exit block: the block in branch_blocks (or branch_entry if empty)
    # whose edge feeds the merge phis.
    exit_block = find_exit_predecessor(merge_phis, branch_blocks, branch_entry)
    blk.terminator = make_yield_for_edge(merge_phis, exit_block, blk, ctx)
end

function set_yield_if_needed!(blk::Block)
    blk.terminator === nothing && (blk.terminator = YieldOp())
end

"""Create an empty branch block with appropriate terminator for its destination."""
function make_empty_branch_block(ctx::StructurizeCtx, dest::Int, from::Int,
                                  merge_phis::Union{Nothing, Vector{MergePhiInfo}},
                                  loop_ctx::Union{Nothing, LoopCtx})
    b = Block()
    # Loop boundary (continue / break)?
    if loop_ctx !== nothing && resolve_loop_exit!(b, ctx, dest, loop_ctx)
        return b
    end
    # Merge phis? Find the phi-edge value this empty arm contributes and yield it.
    if merge_phis !== nothing && !isempty(merge_phis)
        pred = find_exit_predecessor(merge_phis, Set{Int}([dest]), from)
        b.terminator = make_yield_for_edge(merge_phis, pred, b, ctx)
    end
    return b
end

"""
    find_exit_predecessor(merge_phis, blocks, fallback)

The predecessor of the merge whose edge carries this branch's values: the arm
block (in `blocks`) that directly feeds the merge, else the branch source
`fallback`. Single-entry continuations (post `normalize_cf`) guarantee the arm's
exit block is a *direct* merge predecessor — its terminator edge targets the merge
— so a seed/fallback lookup suffices; no reachability search (the old pass-through
BFS dissolved on the block-arg / edge-operand form).
"""
function find_exit_predecessor(merge_phis::Vector{MergePhiInfo}, blocks::Set{Int},
                                fallback::Int)
    seeds = isempty(blocks) ? Set{Int}([fallback]) : blocks
    for b in seeds, phi in merge_phis
        haskey(phi.edge_values, b) && return b
    end
    return fallback
end

"""Create a YieldOp with values from merge phis for a given predecessor edge."""
function make_yield_for_edge(merge_phis::Vector{MergePhiInfo},
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
function set_exit_yield!(blk::Block, ctx::StructurizeCtx,
                          merge_phis::Vector{MergePhiInfo}, last_block::Int)
    pred = find_exit_predecessor(merge_phis, Set{Int}([last_block]), last_block)
    blk.terminator = make_yield_for_edge(merge_phis, pred, blk, ctx)
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
