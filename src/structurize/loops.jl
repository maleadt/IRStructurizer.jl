#=============================================================================
 Branch Region Splitting (dominance-based)
=============================================================================#

"""
    find_branch_regions(ctx, current, true_dest, false_dest, region_blocks, loop_ctx)
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
function find_branch_regions(ctx::StructurizeCtx, current::Int,
                              true_dest::Int, false_dest::Int,
                              region_blocks::Set{Int},
                              loop_ctx::Union{Nothing, LoopCtx}=nothing)
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)

    then_blocks = Set{Int}()
    else_blocks = Set{Int}()

    # Collect blocks dominated by each successor (if single-entry from outside).
    # A successor is "single-entry" if only one predecessor from the region is
    # NOT a loop backedge to it. Loop backedges don't count because the loop body
    # is structurally inside the branch, not a separate entry path.
    if true_dest ∈ region_blocks && true_dest <= nblocks &&
       count_non_backedge_preds(ir, ctx, true_dest, region_blocks) == 1
        collect_dominated!(then_blocks, ctx.domtree, true_dest, region_blocks)
    end

    if false_dest ∈ region_blocks && false_dest <= nblocks &&
       count_non_backedge_preds(ir, ctx, false_dest, region_blocks) == 1
        collect_dominated!(else_blocks, ctx.domtree, false_dest, region_blocks)
    end

    # Remove any overlap with loop bodies that will be handled separately
    # (a block should only be in one region)
    setdiff!(then_blocks, else_blocks)

    # Continuation by exclusion (MLIR `transformToStructuredCFBranches`): the
    # merge is the single distinct target of the edges leaving `current ∪ then ∪
    # else`. A unique target → that's the merge; zero targets → both arms diverge;
    # multiple targets → a multi-entry continuation handled by the multiplexer.
    entries, _ = branch_continuation(ctx, current, true_dest, false_dest,
                                     then_blocks, else_blocks, region_blocks, loop_ctx)
    merge = length(entries) == 1 ? only(entries) : nothing

    return then_blocks, else_blocks, merge
end

"""
    branch_continuation(ctx, current, true_dest, false_dest, then_blocks,
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
function branch_continuation(ctx::StructurizeCtx, current::Int,
                              true_dest::Int, false_dest::Int,
                              then_blocks::Set{Int}, else_blocks::Set{Int},
                              region_blocks::Set{Int},
                              loop_ctx::Union{Nothing, LoopCtx}=nothing)
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)

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
        bb = ir.cfg.blocks[b]
        isempty(bb.succs) && continue   # return-like block: no continuation edge
        for succ in bb.succs
            succ ∈ notContinuation && continue
            # loop boundary (continue/break) — handled by the loop machinery
            if loop_ctx !== nothing &&
               (succ == loop_ctx.header || succ ∉ loop_ctx.loop_blocks)
                continue
            end
            dominates(ctx.domtree, succ, b) && continue   # back-edge to enclosing header
            if succ ∉ seen
                push!(seen, succ)
                push!(entries, succ)
            end
        end
    end
    return entries, notContinuation
end

"""
    find_gated_body(...) -> (body_entry, body_region, merge) | nothing

A short-circuit-guarded body (`if a||b { body }`, `&&`, value forms): the body is
reached from BOTH arms, so it lands in neither then/else region and the branch
continuation has TWO entries. Returns the gated body, its region, and the merge
it exits to; `nothing` if the shape doesn't match (→ ordinary IfOp path).

The continuation is computed MLIR-style (`branch_continuation`), not via `ipdom`
— robust to virtual exits and to a body that fans into `merge` at several
internal points. `emit_gated_branch!` then gates the body under one `scf.if` via
the edge multiplexer, structurized ONCE (no duplication).

Requires: exactly 2 continuation entries; the `body` (dominated by `current`)
exits only to `merge` (which may sit outside `region_blocks` — a nested gated
body's shared outer merge); the body region is fully enclosed (preds from
arms/body, succs to body/merge/return-like); no body value escapes except a phi
value at `merge` (threaded out as a multiplexer result).
"""
function find_gated_body(ctx::StructurizeCtx, current::Int,
                          true_dest::Int, false_dest::Int,
                          then_blocks::Set{Int}, else_blocks::Set{Int},
                          region_blocks::Set{Int},
                          loop_ctx::Union{Nothing, LoopCtx}=nothing)
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)

    entries, _notContinuation = branch_continuation(
        ctx, current, true_dest, false_dest, then_blocks, else_blocks,
        region_blocks, loop_ctx)

    # Only a 2-entry continuation needs the multiplexer (else: ordinary IfOp path).
    length(entries) == 2 || return nothing

    # arms the selector fans into (incl. `current` for the `&&` shape, where
    # false_dest is the body reached directly from current)
    arms = union(then_blocks, else_blocks)
    push!(arms, true_dest); push!(arms, false_dest); push!(arms, current)

    # 2-entry case: gate the `body` (dominated by current, exits only to `merge`),
    # then fall through to `merge`.
    A, B = entries[1], entries[2]
    for (body_entry, merge) in ((A, B), (B, A))
        body_entry == merge && continue
        dominates(ctx.domtree, current, body_entry) || continue
        merge <= nblocks || continue

        # body region = body_entry's dominator subtree, up to (not incl.) `merge`
        dominated = Set{Int}()
        collect_dominated!(dominated, ctx.domtree, body_entry, region_blocks)
        body_region = Set{Int}()
        ok = true
        for b in dominated
            b == merge && continue
            dominates(ctx.domtree, merge, b) && continue
            push!(body_region, b)
        end
        (isempty(body_region) || body_entry ∉ body_region) && continue

        # closure: body preds from arms/body (single entry); succs to body/merge/
        # return-like (throw/unreachable blocks stay nested in the body)
        ok = true
        for b in body_region
            b <= nblocks || (ok = false; break)
            for pred in ir.cfg.blocks[b].preds
                pred ∈ body_region && continue
                if !(b == body_entry && pred ∈ arms)
                    ok = false; break
                end
            end
            ok || break
            for succ in ir.cfg.blocks[b].succs
                (succ ∈ body_region || succ == merge) && continue
                # return-like succ (throw/unreachable): keep it in the body
                if succ <= nblocks && isempty(ir.cfg.blocks[succ].succs) &&
                   succ ∈ region_blocks
                    push!(body_region, succ)
                    continue
                end
                ok = false; break
            end
            ok || break
        end
        ok || continue

        # must be reached from an arm, and not a self-loop entry
        body_entry ∈ ir.cfg.blocks[body_entry].preds && continue
        any(p -> p ∈ arms, ir.cfg.blocks[body_entry].preds) || continue

        # a body value may escape only as a phi value at `merge` (threaded out as a
        # multiplexer result, so def and use share scope); else it'd be stranded → bail
        merge_in_region = merge ∈ region_blocks
        body_defs = Set{Int}()
        for b in body_region, si in first(ir.cfg.blocks[b].stmts):last(ir.cfg.blocks[b].stmts)
            push!(body_defs, si)
        end
        escapes = false
        for blk_idx in 1:nblocks
            blk_idx ∈ body_region && continue
            bb = ir.cfg.blocks[blk_idx]
            for si in first(bb.stmts):last(bb.stmts)
                stmt = ir.stmts.stmt[si]
                if stmt isa PhiNode
                    for k in eachindex(stmt.values)
                        isassigned(stmt.values, k) || continue   # undef phi slot
                        v = stmt.values[k]
                        v isa SSAValue && v.id ∈ body_defs || continue
                        if !(merge_in_region && blk_idx == merge &&
                             Int(stmt.edges[k]) ∈ body_region)
                            escapes = true; break
                        end
                    end
                else
                    for u in stmt_ssa_uses(stmt)
                        if u.id ∈ body_defs
                            escapes = true; break
                        end
                    end
                end
                escapes && break
            end
            escapes && break
        end
        escapes && continue

        return body_entry, body_region, merge
    end
    return nothing
end

"""Count predecessors of `block` in `region` that are not loop backedges to `block`."""
function count_non_backedge_preds(ir::IRCode, ctx::StructurizeCtx, block::Int, region::Set{Int})
    count = 0
    for pred in ir.cfg.blocks[block].preds
        pred ∈ region || continue
        # A backedge is an edge where the target dominates the source
        if dominates(ctx.domtree, block, pred)
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
 Merge Phi Extraction
=============================================================================#

"""Extract phi nodes at `merge_idx` that have edges from blocks in `region`."""
function extract_merge_phis(ir::IRCode, merge_idx::Int, region_blocks::Set{Int})
    result = MergePhiInfo[]
    nblocks = length(ir.cfg.blocks)
    1 <= merge_idx <= nblocks || return result

    bb = ir.cfg.blocks[merge_idx]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa PhiNode || continue

        edge_values = Dict{Int, Any}()
        for (edge_idx, edge) in enumerate(stmt.edges)
            if isassigned(stmt.values, edge_idx)
                # Include edges from region blocks AND direct predecessors
                edge_values[Int(edge)] = stmt.values[edge_idx]
            end
        end
        !isempty(edge_values) && push!(result, MergePhiInfo(si, edge_values))
    end
    return result
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
    ir = ctx.ir

    # 1. Extract header phi nodes
    phi_info = extract_loop_phis(ir, header, loop_blocks)

    # 2. Find exit destination (prefer the post-dominator of the header —
    #    the structurally correct continuation, not an error/unreachable path)
    exit_dest = find_loop_exit(ctx, header, loop_blocks)

    # 3. Find extra exit values (loop-internal SSAs used outside)
    already_exported = Set{Int}(p.ssa_idx for p in phi_info)
    extra_exits = find_extra_exit_values(ir, loop_blocks, already_exported)

    # 4. Build init/carried values and block arguments
    init_values = IRValue[]
    carried_values = IRValue[]
    phi_indices = Int[]
    phi_types = Any[]
    body = Block()
    subs = Dict{Int, BlockArgument}()

    for phi in phi_info
        # If a preceding IfOp already defined this phi SSA (via getfield),
        # use that as init_val — it captures the correct branch-selected value.
        init_val = haskey(block.body, phi.ssa_idx) ? SSAValue(phi.ssa_idx) : phi.entry_val
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
        # `ex.type` bypasses `ctx.types`, so widen it here too.
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

    # 7. Emit LoopOp + getfields
    # Anchor debug info to the loop header's first statement
    header_anchor = first(ir.cfg.blocks[header].stmts)

    loop_op = LoopOp(body, init_values)
    loop_ssa = alloc_ssa!(ctx)
    result_type = Tuple{phi_types...}
    push!(block, loop_ssa, loop_op, result_type)
    anchor_line!(ctx, loop_ssa, header_anchor)

    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
        # If a preceding IfOp already defined this phi SSA (multi-entry header),
        # use a fresh index for the loop's getfield to avoid SSA uniqueness violation.
        # Downstream code references phi_idx which is the IfOp's definition;
        # the loop result is accessed via the fresh index (only used if phi changes in loop).
        idx = haskey(block.body, phi_idx) ? alloc_ssa!(ctx) : phi_idx
        push!(block, idx, Expr(:call, Core.getfield, SSAValue(loop_ssa), i), phi_type)
        idx != phi_idx && anchor_line!(ctx, idx, header_anchor)
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

"""Extract phi nodes from a loop header, separating entry and carried values."""
function extract_loop_phis(ir::IRCode, header::Int, loop_blocks::Set{Int})
    result = LoopPhiInfo[]
    bb = ir.cfg.blocks[header]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa PhiNode || continue
        entry_val = nothing
        carried_val = nothing
        for (edge_idx, edge) in enumerate(stmt.edges)
            isassigned(stmt.values, edge_idx) || continue
            val = stmt.values[edge_idx]
            if Int(edge) ∈ loop_blocks
                carried_val = val
            else
                entry_val = val
            end
        end
        if entry_val !== nothing && carried_val !== nothing
            push!(result, LoopPhiInfo(si, entry_val, carried_val))
        elseif entry_val !== nothing || carried_val !== nothing
            # A phi with edges from only one side of the loop boundary is
            # malformed — the optimizer may have removed a dead edge, or
            # the loop has unusual structure. Error rather than silently
            # producing wrong loop-carried values.
            has_entry = entry_val !== nothing
            error("internal error: loop header phi %$si at BB$header has ",
                  has_entry ? "entry" : "carried", " value but no ",
                  has_entry ? "carried" : "entry", " value")
        end
    end
    result
end

"""
Find the primary exit destination of a loop.

Prefers the immediate post-dominator of the header (the structurally correct
continuation point). Falls back to any exit with successors (non-dead-end),
then any exit at all.
"""
function find_loop_exit(ctx::StructurizeCtx, header::Int, loop_blocks::Set{Int})
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)
    exits = Int[]
    for b in loop_blocks
        for succ in ir.cfg.blocks[b].succs
            succ ∉ loop_blocks && succ ∉ exits && push!(exits, succ)
        end
    end
    isempty(exits) && return nothing
    length(exits) == 1 && return exits[1]
    # Prefer post-dominator of header (the natural continuation)
    ipdom = ctx.postdomtree.idoms_bb[header]
    ipdom != 0 && ipdom ∉ loop_blocks && ipdom in exits && return ipdom
    # Fall back: prefer exits with successors, then non-throw dead-ends
    for e in exits
        e <= nblocks && !isempty(ir.cfg.blocks[e].succs) && return e
    end
    for e in exits
        if e <= nblocks && isempty(ir.cfg.blocks[e].succs)
            ir.stmts.type[last(ir.cfg.blocks[e].stmts)] !== Union{} && return e
        end
    end
    return first(exits)
end

"""Find all blocks outside `loop_blocks` that are successors of loop blocks."""
function find_loop_exits(ir::IRCode, loop_blocks::Set{Int})
    exits = Set{Int}()
    for b in loop_blocks
        for succ in ir.cfg.blocks[b].succs
            succ ∉ loop_blocks && push!(exits, succ)
        end
    end
    exits
end

"""
Find loop-internal SSA values referenced outside the loop.

Scans blocks reachable from loop exit edges (not the entire IR). This is more
precise than scanning all non-loop blocks: it excludes blocks before the loop
or on branches that bypass it. Values escape through exit-block phis, direct
references at downstream blocks, or as operands of sequential loops.
"""
function find_extra_exit_values(ir::IRCode, loop_blocks::Set{Int},
                                 already_exported::Set{Int})
    result = @NamedTuple{ssa_idx::Int, value::Any, type::Any}[]
    seen = Set{Int}()

    # Collect non-loop blocks reachable from loop exit edges.
    # Skip throw/unreachable blocks (terminal type Union{}): these are error
    # paths whose values don't need threading because find_loop_exit prefers
    # non-throw continuations, so throw blocks are not walked after the loop.
    reachable = Set{Int}()
    worklist = Int[]
    nblocks = length(ir.cfg.blocks)
    for b in loop_blocks
        for succ in ir.cfg.blocks[b].succs
            succ ∉ loop_blocks || continue
            # Skip throw/unreachable blocks
            if succ <= nblocks && isempty(ir.cfg.blocks[succ].succs) &&
               ir.stmts.type[last(ir.cfg.blocks[succ].stmts)] === Union{}
                continue
            end
            push!(worklist, succ)
        end
    end
    while !isempty(worklist)
        b = pop!(worklist)
        b ∈ reachable && continue
        b ∈ loop_blocks && continue
        push!(reachable, b)
        for succ in ir.cfg.blocks[b].succs
            succ ∉ reachable && succ ∉ loop_blocks && push!(worklist, succ)
        end
    end

    for blk_idx in reachable
        bb = ir.cfg.blocks[blk_idx]
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa PhiNode
                si ∈ already_exported && continue
                for (edge_idx, edge) in enumerate(stmt.edges)
                    if isassigned(stmt.values, edge_idx) && Int(edge) ∈ loop_blocks
                        loop_val = stmt.values[edge_idx]
                        gf_idx = loop_val isa SSAValue ? loop_val.id : si
                        gf_idx ∈ seen && continue
                        gf_idx ∈ already_exported && continue
                        push!(result, (; ssa_idx=gf_idx, value=loop_val, type=ir.stmts.type[si]))
                        push!(seen, gf_idx)
                    end
                end
            else
                # Single-predecessor exit blocks may reference loop values directly
                for arg in stmt_ssa_uses(stmt)
                    is_defined_in(arg, loop_blocks, ir) || continue
                    arg.id ∈ already_exported && continue
                    arg.id ∈ seen && continue
                    push!(result, (; ssa_idx=arg.id, value=arg, type=ir.stmts.type[arg.id]))
                    push!(seen, arg.id)
                end
            end
        end
    end
    result
end

function stmt_ssa_uses(@nospecialize(stmt))
    if stmt isa SSAValue
        return (stmt,)
    elseif stmt isa Expr
        return Iterators.filter(x -> x isa SSAValue, stmt.args)
    elseif stmt isa GotoIfNot && stmt.cond isa SSAValue
        return (stmt.cond,)
    elseif stmt isa ReturnNode && isdefined(stmt, :val) && stmt.val isa SSAValue
        return (stmt.val,)
    elseif stmt isa PiNode && stmt.val isa SSAValue
        # A `PiNode`'s refined value is a real use — without this, a post-loop
        # type-assertion on a loop-internal SSA isn't threaded out as an exit.
        return (stmt.val,)
    else
        return ()
    end
end

function is_defined_in(val::SSAValue, blocks::Set{Int}, ir::IRCode)
    for blk_idx in blocks
        bb = ir.cfg.blocks[blk_idx]
        val.id in first(bb.stmts):last(bb.stmts) && return true
    end
    false
end
is_defined_in(val, blocks, ir) = false
