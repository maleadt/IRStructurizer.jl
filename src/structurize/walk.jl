#=============================================================================
 Core Algorithm — the lift, reading the explicit-edge `MBlock` form directly.

 Block arguments + per-edge operands replace Julia phi nodes (the MLIR model), so
 "what value does predecessor P contribute to block B's k-th argument" is just the
 operand on edge P→B (`edge_operands`) — no phi-node scanning, no dense round-trip.
=============================================================================#

"""
    MergeInfo

The merge/continuation block of an `IfOp`, in native block-argument form. `merge`
is the block id; `positions` are the indices of its block args that are *live*
(some predecessor edge carries a real, non-`Undef` operand) and so become `IfOp`
results; `ids`/`types` are those args' stable ids and (widened) types. Built once
by [`merge_info`](@ref).

Each arm's `YieldOp` is then just the operands *its own* exit edge carries to
`merge` — `edge_operands(m, arm_exit, merge)` read position by position — instead
of a predecessor-keyed phi reconstruction with a reverse edge lookup. "What value
does this arm contribute to the merge's k-th arg" *is* the k-th operand on the
arm's edge (the MLIR model).
"""
struct MergeInfo
    merge::Int
    positions::Vector{Int}
    ids::Vector{Int}
    types::Vector{Any}
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
                              merge_phis::Union{Nothing, MergeInfo}=nothing,
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

    # Region ended — yield to the merge if not already terminated. The arm's exit
    # block is the walk's tracked `last_block`; its edge to the merge carries the
    # yield operands directly.
    if block.terminator === nothing && merge_phis !== nothing
        yield_to_merge!(block, ctx, last_block, merge_phis)
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

"""
    emit_branch!(block, ctx, current, condbr, region_blocks, outer_merge_phis) -> next

Create an IfOp for a conditional branch. Returns the merge block index to
continue with, or nothing if both branches exit/diverge.
"""
function emit_branch!(block::Block, ctx::StructurizeCtx, current::Int,
                      condbr::MCondBr, region_blocks::Set{Int},
                      outer_merge_phis::Union{Nothing, MergeInfo},
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

    # If merge exists and is in region, read its block args (the "phis") as a
    # MergeInfo. Skip args at loop headers: a header is never a branch merge now —
    # the pre-header (`normalize_one_preheader!`) routes every multi-entry header's
    # entry edges through a pre-header, so the branch's continuation is that
    # pre-header, not the header itself.
    #
    # Continuation-by-exclusion finds the *real* merge directly, so a no-arg merge
    # is genuinely arg-free: the walk continues through it without a separate
    # pass-through step. A no-arg merge yields `nothing` here.
    merge_phis = if merge !== nothing && merge ∈ region_blocks && !haskey(ctx.loop_map, merge)
        merge_info(ctx, merge)
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
        set_branch_yields!(then_blk, ctx, merge_phis, then_blocks, current)
        set_branch_yields!(else_blk, ctx, merge_phis, else_blocks, current)

        if_op = IfOp(cond, then_blk, else_blk)
        emit_ifop_result!(block, if_op, merge_phis.ids, merge_phis.types, ctx, branch_anchor)
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

        if outer_merge_phis !== nothing
            phi_types = outer_merge_phis.types
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

"""Set `blk`'s terminator to the `YieldOp` carrying what `exit_block` contributes
to `minfo.merge`: for each live merge-arg position, the operand on edge `exit_block
→ merge` (`edge_operands`), remapped through `ssa_remap`. The arm yields *its own*
edge — no predecessor-keyed reconstruction.

`Undef` (an unassigned phi slot) or a missing edge (`exit_block` does not reach the
merge — an arm that diverged, whose yield is then dead) becomes a typed `Undef`. If
the arm already redefines a merge arg at its (remapped) id — e.g. a nested IfOp on
the same merge emitted the `getfield` there — that in-block definition is preferred
over the raw edge operand."""
function yield_to_merge!(blk::Block, ctx::StructurizeCtx, exit_block::Int, minfo::MergeInfo)
    ops = edge_operands(ctx.m::MCFG, exit_block, minfo.merge)
    vals = IRValue[]
    for (j, k) in enumerate(minfo.positions)
        v = ops === nothing ? Undef(minfo.types[j]) : ops[k]
        if v isa Undef
            push!(vals, Undef(minfo.types[j]))
        else
            v = remap_ssa_ref(v, ctx.ssa_remap)
            idx = get(ctx.ssa_remap, minfo.ids[j], minfo.ids[j])
            push!(vals, haskey(blk.body, idx) ? SSAValue(idx) : v)
        end
    end
    blk.terminator = YieldOp(vals)
end

"""The arm's exit block: the seed (in `blocks`, else the branch source `fallback`)
whose edge targets `merge`. Single-entry continuations (post `normalize_cf`)
guarantee the arm's exit is a *direct* merge predecessor, so a seed lookup
suffices — no reachability search. `fallback` is returned when no seed reaches the
merge (an arm that diverged); `yield_to_merge!` then yields dead `Undef`s."""
function branch_exit_block(ctx::StructurizeCtx, merge::Int, blocks::Set{Int}, fallback::Int)
    m = ctx.m::MCFG
    for b in (isempty(blocks) ? (fallback,) : blocks)
        edge_operands(m, b, merge) !== nothing && return b
    end
    return fallback
end

"""Set the yield terminator on an arm block, if not already set (a `ReturnNode` /
inner yield takes precedence). The exit block is the arm block that reaches the
merge directly."""
function set_branch_yields!(blk::Block, ctx::StructurizeCtx, minfo::MergeInfo,
                            branch_blocks::Set{Int}, branch_entry::Int)
    blk.terminator !== nothing && return
    yield_to_merge!(blk, ctx, branch_exit_block(ctx, minfo.merge, branch_blocks, branch_entry), minfo)
end

function set_yield_if_needed!(blk::Block)
    blk.terminator === nothing && (blk.terminator = YieldOp())
end

"""Create an empty branch arm's block. The arm is just the edge `from → dest`, so
when `dest` is the merge the block yields the operands that edge carries
(`from`'s edge to the merge); a loop boundary becomes a break/continue instead."""
function make_empty_branch_block(ctx::StructurizeCtx, dest::Int, from::Int,
                                  minfo::Union{Nothing, MergeInfo},
                                  loop_ctx::Union{Nothing, LoopCtx})
    b = Block()
    if loop_ctx !== nothing && resolve_loop_exit!(b, ctx, dest, loop_ctx)
        return b
    end
    minfo !== nothing && yield_to_merge!(b, ctx, from, minfo)
    return b
end
