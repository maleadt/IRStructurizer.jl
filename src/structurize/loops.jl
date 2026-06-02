#=============================================================================
 Branch Region Splitting (dominance-based)

 These analyses read only CFG topology + dominance (`cfg`/`domtree`), so they run
 unchanged whether the CFG comes from `ir.cfg` or `build_cfg(m)`. The lift passes
 `ctx.cfg`/`ctx.domtree`; `normalize_one_continuation!` passes a fresh pair.
=============================================================================#

"""
    find_branch_regions(cfg, domtree, current, true_dest, false_dest, region_blocks, loop_ctx)
        -> (then_blocks, else_blocks, merge)

Split region_blocks into then/else regions using dominance, and select the merge
(continuation) block by exclusion (`branch_continuation`).

A successor with a single non-backedge predecessor gets all blocks it dominates
(MLIR's edge-domination test, `CFGToSCF.cpp:981`). A successor with multiple
predecessors is a merge block (empty arm region).

The merge is the *single* common target of the edges leaving the branch — i.e.
`branch_continuation` returning exactly one entry. When the continuation is
absent (both arms diverge) or has more than one entry (a multi-entry
continuation that needs the edge multiplexer), `merge` is `nothing` and the
caller routes accordingly. Post-dominance never enters as an ordering key, so
the result depends only on CFG topology + dominance (invariant I1).
"""
function find_branch_regions(cfg::CFG, domtree::DomTree, current::Int,
                              true_dest::Int, false_dest::Int,
                              region_blocks::Set{Int},
                              loop_ctx::Union{Nothing, LoopCtx}=nothing)
    nblocks = length(cfg.blocks)

    then_blocks = Set{Int}()
    else_blocks = Set{Int}()

    # Collect blocks dominated by each successor (if single-entry from outside).
    # A successor is "single-entry" if only one predecessor from the region is
    # NOT a loop backedge to it. Loop backedges don't count because the loop body
    # is structurally inside the branch, not a separate entry path.
    if true_dest ∈ region_blocks && true_dest <= nblocks &&
       count_non_backedge_preds(cfg, domtree, true_dest, region_blocks) == 1
        collect_dominated!(then_blocks, domtree, true_dest, region_blocks)
    end

    if false_dest ∈ region_blocks && false_dest <= nblocks &&
       count_non_backedge_preds(cfg, domtree, false_dest, region_blocks) == 1
        collect_dominated!(else_blocks, domtree, false_dest, region_blocks)
    end

    # Remove any overlap with loop bodies that will be handled separately
    # (a block should only be in one region)
    setdiff!(then_blocks, else_blocks)

    # Continuation by exclusion (MLIR `transformToStructuredCFBranches`): the
    # merge is the single distinct target of the edges leaving `current ∪ then ∪
    # else`. A unique target → that's the merge; zero targets → both arms diverge;
    # multiple targets → a multi-entry continuation handled by the multiplexer.
    entries, _ = branch_continuation(cfg, domtree, current, true_dest, false_dest,
                                     then_blocks, else_blocks, region_blocks, loop_ctx)
    merge = length(entries) == 1 ? only(entries) : nothing

    return then_blocks, else_blocks, merge
end

"""
    branch_continuation(cfg, domtree, current, true_dest, false_dest, then_blocks,
                         else_blocks, region_blocks)
        -> (continuation_entries::Vector{Int}, notContinuation::Set{Int})

Compute the branch continuation MLIR-style, mirroring
`transformToStructuredCFBranches` in CFGToSCF.cpp (~lines 969-1098).

`notContinuation` (CFGToSCF.cpp `notContinuation`) = `current` plus every block
SOLELY dominated by one of the branch successors — exactly `then_blocks` and
`else_blocks` (each is the dominator subtree of a single-predecessor successor,
which is how `find_branch_regions` already computes them; CFGToSCF.cpp lines
977-990).

The continuation is then derived from the **edges leaving `notContinuation`**
(CFGToSCF.cpp lines 1054-1090, the `continuationEdges` loop), NOT from
post-dominance. This is the part that makes the analysis robust to virtual exits
(throw/`÷`/undef paths give `ipdom == 0`) and to bodies that fan into the
continuation at several internal points: every such region-exit edge target is a
continuation entry. Region-exit/return-like blocks (no successors, CFGToSCF.cpp
`isRegionExitBlock`) contribute nothing here — they stay as case-2 unstructured
sub-regions handled by the recursive walk. The distinct edge targets are the
continuation entry blocks, deduplicated preserving first-seen order.

A continuation entry may leave `region_blocks` entirely: when a gated body is
NESTED in another, the inner branch's skip path targets the SHARED outer merge,
which the outer multiplexer left out of the inner region. We therefore keep
out-of-region targets as entries, but DROP loop boundaries (`loop_ctx`): a
back-edge to the header is a continue and an edge out of the loop is a break —
neither is part of this branch's forward continuation.
"""
function branch_continuation(cfg::CFG, domtree::DomTree, current::Int,
                              true_dest::Int, false_dest::Int,
                              then_blocks::Set{Int}, else_blocks::Set{Int},
                              region_blocks::Set{Int},
                              loop_ctx::Union{Nothing, LoopCtx}=nothing)
    nblocks = length(cfg.blocks)

    # notContinuation = branch entry ∪ arm regions; continuation = distinct
    # targets of edges leaving it (edge targets, not post-dominance → survives
    # virtual exits). MLIR transformToStructuredCFBranches:
    # https://github.com/llvm/llvm-project/blob/cabad14763b27802296b44b3b5e507f6a4f7a3c5/mlir/lib/Transforms/Utils/CFGToSCF.cpp
    notContinuation = Set{Int}((current,))
    union!(notContinuation, then_blocks)
    union!(notContinuation, else_blocks)

    scan = Int[current]
    append!(scan, then_blocks)
    append!(scan, else_blocks)

    entries = Int[]
    seen = Set{Int}()
    for b in scan
        1 <= b <= nblocks || continue
        bb = cfg.blocks[b]
        isempty(bb.succs) && continue   # return-like block: no continuation edge
        for succ in bb.succs
            succ ∈ notContinuation && continue
            # loop boundary (continue/break) — handled by the loop machinery
            if loop_ctx !== nothing &&
               (succ == loop_ctx.header || succ ∉ loop_ctx.loop_blocks)
                continue
            end
            dominates(domtree, succ, b) && continue   # back-edge to enclosing header
            if succ ∉ seen
                push!(seen, succ)
                push!(entries, succ)
            end
        end
    end
    return entries, notContinuation
end

"""Count predecessors of `block` in `region` that are not loop backedges to `block`."""
function count_non_backedge_preds(cfg::CFG, domtree::DomTree, block::Int, region::Set{Int})
    count = 0
    for pred in cfg.blocks[block].preds
        pred ∈ region || continue
        # A backedge is an edge where the target dominates the source
        if dominates(domtree, block, pred)
            continue  # skip loop backedge
        end
        count += 1
    end
    count
end


"""Collect all blocks in `region` dominated by `root` (including root itself)."""
function collect_dominated!(result::Set{Int}, domtree::DomTree, root::Int, region::Set{Int})
    root ∈ region || return
    push!(result, root)
    for child in domtree.nodes[root].children
        child ∈ region && collect_dominated!(result, domtree, child, region)
    end
end

#=============================================================================
 Merge result shape (block args + per-edge operands)
=============================================================================#

"""Read the merge block `merge_idx`'s block arguments as a [`MergeInfo`](@ref): the
*live* arg positions — those some predecessor edge assigns a real (non-`Undef`)
operand — become the `IfOp`'s results. An arg every predecessor leaves `Undef` is a
dead phi slot and is dropped (no result). Returns `nothing` if no arg is live. The
MBlock analogue of reading a merge block's leading phi nodes, but recording only
the result *shape*: each arm later yields its own edge's operands directly
(`yield_to_merge!`), so there is no per-predecessor value map here."""
function merge_info(ctx::StructurizeCtx, merge_idx::Int)
    m = ctx.m::MCFG
    1 <= merge_idx <= length(m.blocks) || return nothing
    args = m.blocks[merge_idx].args
    isempty(args) && return nothing
    preds = ctx.cfg.blocks[merge_idx].preds
    positions = Int[]; ids = Int[]; types = Any[]
    for (k, arg) in enumerate(args)
        any(p -> (o = edge_operands(m, p, merge_idx); o !== nothing && !(o[k] isa Undef)), preds) || continue
        push!(positions, k); push!(ids, arg); push!(types, get(ctx.types, arg, Any))
    end
    isempty(ids) ? nothing : MergeInfo(merge_idx, positions, ids, types)
end

#=============================================================================
 IfOp Result Emission
=============================================================================#

"""Push an IfOp and generate getfield statements at each phi index.
`line_anchor` is the SSA index to inherit debug info from (typically the branch terminator)."""
function emit_ifop_result!(block::Block, if_op::IfOp, phi_indices::Vector{Int},
                            phi_types::AbstractVector, ctx::StructurizeCtx,
                            line_anchor::Int=0)
    if_ssa = alloc_ssa!(ctx)
    remap = ctx.ssa_remap
    if !isempty(phi_indices)
        # `phi_types` come pre-widened from `ctx.types`.
        result_type = Tuple{phi_types...}
        push!(block, if_ssa, if_op, result_type)
        line_anchor != 0 && anchor_line!(ctx, if_ssa, line_anchor)
        for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
            idx = get(remap, phi_idx, phi_idx)
            push!(block, idx, Expr(:call, Core.getfield, SSAValue(if_ssa), i), phi_type)
            idx != phi_idx && anchor_line!(ctx, idx, line_anchor != 0 ? line_anchor : phi_idx)
        end
    else
        push!(block, if_ssa, if_op, Tuple{})
        line_anchor != 0 && anchor_line!(ctx, if_ssa, line_anchor)
    end
    return if_ssa
end

#=============================================================================
 Loop Lifting (LoopOp)
=============================================================================#

"""
    emit_loop!(block, ctx, header, loop_blocks, region_blocks) -> exit_dest

Build a LoopOp for the natural loop at `header` and emit it into `block`.
Returns the exit destination block (may be outside region_blocks).
"""
function emit_loop!(block::Block, ctx::StructurizeCtx, header::Int,
                     loop_blocks::Set{Int}, region_blocks::Set{Int})
    # 1. Header block arguments (the loop's phis), as entry/carried value pairs.
    phi_info = extract_loop_phis(ctx, header, loop_blocks)

    # 2. The loop's single exit — its one non-loop successor. The single-exiting
    #    latch (normalize_cf) unified every multi-exit loop to one exit edge, so
    #    there is no choice to make: no post-dominance preference, no block-index
    #    tie-break (the old `find_loop_exit` I1 leak — gone).
    exit_dest = single_loop_exit(ctx, loop_blocks)

    # 3. Escaping values: every loop-internal value used outside the loop. After
    #    reduce form (normalize_cf) the latch carries the escapees as block args,
    #    so this is a flat used-outside scan — no post-loop BFS, no remap-vs-merge
    #    collision (the old `find_extra_exit_values`).
    already_exported = Set{Int}(p.ssa_idx for p in phi_info)
    extra_exits = loop_escaping_values(ctx, loop_blocks, already_exported)

    # 4. Build init/carried values and block arguments
    init_values = IRValue[]
    carried_values = IRValue[]
    phi_indices = Int[]
    phi_types = Any[]
    body = Block()
    subs = Dict{Int, BlockArgument}()

    for phi in phi_info
        # The entry value comes through the pre-header: a header is single-entry
        # from outside (`normalize_one_preheader!`), so its one entry edge carries
        # the merged init (a branch selection / irreducible discriminator computed
        # by the IfOp that yields into the pre-header). Remap through `ssa_remap`
        # (a single-edge pre-header arg may have been renamed, not emitted at its
        # own index).
        init_val = remap_ssa_ref(phi.entry_val, ctx.ssa_remap)
        push!(init_values, init_val)
        push!(carried_values, phi.carried_val)
        push!(phi_indices, phi.ssa_idx)
        push!(phi_types, ctx.types[phi.ssa_idx])
        arg = BlockArgument(alloc_arg!(ctx), ctx.types[phi.ssa_idx])
        push!(body.args, arg)
        subs[phi.ssa_idx] = arg
    end

    # Save remap state and add extra-exit remappings for the loop body.
    # Inner defs get fresh indices; outer getfields keep the originals.
    saved_remap = copy(ctx.ssa_remap)
    for ex in extra_exits
        fresh = alloc_ssa!(ctx)
        ctx.ssa_remap[ex.ssa_idx] = fresh
        anchor_line!(ctx, fresh, ex.ssa_idx)
        # `ex.type` is already widened (`ctx.types`), but stay robust.
        ext = widenconst(ex.type)
        push!(init_values, Undef(ext))
        push!(carried_values, SSAValue(fresh))  # carry the fresh-index value
        push!(phi_indices, ex.ssa_idx)           # getfield OUTSIDE uses original
        push!(phi_types, ext)
        arg = BlockArgument(alloc_arg!(ctx), ext)
        push!(body.args, arg)
    end

    # Remap header phi carried values that reference extra exit SSAs
    if !isempty(ctx.ssa_remap)
        n_header = length(phi_info)
        for i in 1:n_header
            v = carried_values[i]
            if v isa SSAValue
                carried_values[i] = SSAValue(get(ctx.ssa_remap, v.id, v.id))
            end
        end
    end

    # 5. Build loop body
    build_loop_body!(body, ctx, header, loop_blocks, carried_values, subs)

    # Restore remap (scoped to loop body)
    ctx.ssa_remap = saved_remap

    # 6. Apply phi→arg substitutions
    apply_substitutions!(body, subs, ctx)

    # 7. Emit LoopOp + getfields. Anchor debug info to the header's first stmt.
    header_anchor = first_body_id(ctx, header)

    loop_op = LoopOp(body, init_values)
    loop_ssa = alloc_ssa!(ctx)
    result_type = Tuple{phi_types...}
    push!(block, loop_ssa, loop_op, result_type)
    anchor_line!(ctx, loop_ssa, header_anchor)

    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
        # The loop result lands at the header arg's own id: a header is never a
        # branch merge (the pre-header is), so `phi_idx` is not pre-defined by an
        # enclosing IfOp — no fresh-index dance, and post-loop uses of `phi_idx`
        # resolve to this result (ISSUES.md #2 fixed).
        push!(block, phi_idx, Expr(:call, Core.getfield, SSAValue(loop_ssa), i), phi_type)
    end

    return exit_dest
end

#=============================================================================
 Loop Body Construction
=============================================================================#

"""
Build the body of a LoopOp using `structurize_region!` with a LoopCtx.
The LoopCtx makes the region walk loop-aware: back-edges → ContinueOp, exits → BreakOp.
"""
function build_loop_body!(body::Block, ctx::StructurizeCtx, header::Int,
                           loop_blocks::Set{Int}, carried_values::Vector{IRValue},
                           subs::Dict{Int, BlockArgument})
    break_values = IRValue[arg for arg in body.args]
    # Extra exits (beyond header phis) must carry the current iteration's
    # computed value, not the stale block arg from the previous iteration.
    n_header_phis = length(subs)
    for i in (n_header_phis + 1):length(break_values)
        break_values[i] = carried_values[i]
    end
    lctx = LoopCtx(header, loop_blocks, carried_values, break_values)

    # Use structurize_region! with loop context for the entire loop body
    content = structurize_region!(ctx, header, loop_blocks; loop_ctx=lctx)

    # Merge content into the pre-existing body (which already has args)
    merge_block_into!(body, content)
end

function merge_block_into!(dst::Block, src::Block)
    for (idx, entry) in src.body
        push!(dst.body, (idx, entry.stmt, entry.type, entry.flag))
    end
    if src.terminator !== nothing && dst.terminator === nothing
        dst.terminator = src.terminator
    end
end

#=============================================================================
 Loop Analysis Helpers
=============================================================================#

struct LoopPhiInfo
    ssa_idx::Int
    entry_val::Any
    carried_val::Any
end

"""Extract a loop header's block arguments, separating each into its entry value
(operand on an edge from outside the loop) and carried value (operand on the back
edge from inside the loop). The single-exiting latch / entry mux guarantee one of
each, so an argument with only one side is malformed (a dead edge the optimizer
left, or unexpected loop structure) — error rather than emit wrong carries."""
function extract_loop_phis(ctx::StructurizeCtx, header::Int, loop_blocks::Set{Int})
    m = ctx.m::MCFG
    result = LoopPhiInfo[]
    preds = ctx.cfg.blocks[header].preds
    for (k, arg) in enumerate(m.blocks[header].args)
        entry_val = nothing
        carried_val = nothing
        for p in preds
            ops = edge_operands(m, p, header)
            ops === nothing && continue
            v = ops[k]
            v isa Undef && continue
            if p ∈ loop_blocks
                carried_val = v
            else
                entry_val = v
            end
        end
        if entry_val !== nothing && carried_val !== nothing
            push!(result, LoopPhiInfo(arg, entry_val, carried_val))
        elseif entry_val !== nothing || carried_val !== nothing
            has_entry = entry_val !== nothing
            error("internal error: loop header arg %$arg at BB$header has ",
                  has_entry ? "entry" : "carried", " value but no ",
                  has_entry ? "carried" : "entry", " value")
        end
    end
    result
end

"""The loop's single exit: its one successor outside `loop_blocks`, or `nothing`
(a statically-infinite loop / all escapes are region-exits). The single-exiting
latch (`normalize_cf`) unifies every multi-exit loop to one exit edge, so this is
unambiguous — no post-dominance preference, no block-index tie-break (the old
`find_loop_exit` I1 leak). More than one would mean the latch failed to fire."""
function single_loop_exit(ctx::StructurizeCtx, loop_blocks::Set{Int})
    exits = find_loop_exits(ctx, loop_blocks)
    isempty(exits) && return nothing
    length(exits) == 1 && return only(exits)
    error("internal error: loop has ", length(exits), " exit edges; the single-",
          "exiting latch (normalize_cf) should have unified them to one")
end

"""Find all blocks outside `loop_blocks` that are successors of loop blocks."""
function find_loop_exits(ctx::StructurizeCtx, loop_blocks::Set{Int})
    exits = Set{Int}()
    for b in loop_blocks
        for succ in ctx.cfg.blocks[b].succs
            succ ∉ loop_blocks && push!(exits, succ)
        end
    end
    exits
end

"""
Loop-internal SSA values referenced from outside the loop, threaded out as loop
results. A value escapes when it is used at a position *not strictly inside* the
loop, classified by where the operand is consumed:

- a body statement / terminator operand of a **non-loop** block, or
- an **edge operand on an edge whose target is non-loop** — a value carried out of
  the loop into a successor's block argument (the MBlock form of the old "exit
  phi": the loop-exit edge's operand lives on the *in-loop* latch, but it feeds a
  *non-loop* block's arg, so it escapes).

Deterministic block/operand order; `already_exported` skips the header phis (which
are already loop-carried). Over-approximation is impossible — every reported value
genuinely has an outside use — and `promote_loops!` drops any that the LoopOp
doesn't need.
"""
function loop_escaping_values(ctx::StructurizeCtx, loop_blocks::Set{Int},
                              already_exported::Set{Int})
    m = ctx.m::MCFG
    result = @NamedTuple{ssa_idx::Int, type::Any}[]
    seen = Set{Int}()
    function consider(@nospecialize(v))
        v isa SSAValue || return
        id = v.id
        (get(ctx.def_block, id, 0) ∈ loop_blocks) || return
        (id ∈ already_exported || id ∈ seen) && return
        push!(result, (; ssa_idx=id, type=get(ctx.types, id, Any)))
        push!(seen, id)
    end
    for (bid, b) in enumerate(m.blocks)
        # Body + terminator operands escape only from a non-loop block.
        if bid ∉ loop_blocks
            for s in b.body
                remap_ssa(s.stmt, v -> (consider(v); v))
            end
            t = b.term
            if t isa MCondBr
                consider(t.cond)
            elseif t isa MReturn
                t.has_val && consider(t.val)
            end
        end
        # An edge operand escapes when the edge leaves the loop (target ∉ loop):
        # a loop-internal value carried into the non-loop successor's block args.
        t = b.term
        edges = t isa MGoto ? (t.edge,) : t isa MCondBr ? (t.t, t.f) : ()
        for e in edges
            e.target ∈ loop_blocks && continue
            for v in e.args
                consider(v)
            end
        end
    end
    result
end
