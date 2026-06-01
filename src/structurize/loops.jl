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
    extra_exits = find_extra_exit_values(ir, loop_blocks, already_exported, exit_dest)

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
    build_loop_body!(body, ctx, header, loop_blocks, carried_values, subs, exit_dest)

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
                           subs::Dict{Int, BlockArgument},
                           exit_dest::Union{Int, Nothing})
    break_values = IRValue[arg for arg in body.args]
    # Extra exits (beyond header phis) must carry the current iteration's
    # computed value, not the stale block arg from the previous iteration.
    n_header_phis = length(subs)
    for i in (n_header_phis + 1):length(break_values)
        break_values[i] = carried_values[i]
    end
    lctx = LoopCtx(header, loop_blocks, carried_values, break_values, exit_dest)

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
Find the loop's *primary* exit: where control goes when the loop stops iterating
normally — the continuation. The loop breaks to it and its loop values are
threaded out as results. A *secondary* exit (an early `return`/`throw` reached
mid-body) is re-materialized in place instead (invariant I8).

The primary exit is taken at the loop's "keep iterating?" decision, so its source
block is adjacent to the back edge: it branches to the exit on one side and, on
the other, to the loop header or a latch (a back-edge source). An irreducible
loop's mux header dispatches *into* the loop and its latch only loops back, so no
block is both an exit source and back-edge-adjacent → there is no primary exit
(`nothing`): every escape is an early return, re-materialized, and the loop has
no break/result.

Layout-independent (invariant I1): candidates are sorted and the header's
post-dominator is preferred; nothing keys on raw block order. (MLIR's
single-exiting latch removes this choice entirely — the M4 cleanup.)
"""
function find_loop_exit(ctx::StructurizeCtx, header::Int, loop_blocks::Set{Int})
    ir = ctx.ir
    exits = sort!(collect(find_loop_exits(ir, loop_blocks)))
    isempty(exits) && return nothing
    length(exits) == 1 && return exits[1]
    latches = Set{Int}(b for b in loop_blocks if header in ir.cfg.blocks[b].succs)
    backedge_adjacent(b) = header in ir.cfg.blocks[b].succs ||
                           any(s -> s in latches, ir.cfg.blocks[b].succs)
    cands = sort!([e for e in exits
                   if any(b -> e in ir.cfg.blocks[b].succs && backedge_adjacent(b), loop_blocks)])
    isempty(cands) && return nothing
    length(cands) == 1 && return cands[1]
    ipdom = ctx.postdomtree.idoms_bb[header]
    ipdom != 0 && ipdom in cands && return ipdom
    return first(cands)
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

Scans the post-loop region reachable from the *primary* exit (`exit_dest`), not
every exit edge: a value only needs threading out if it is read at the loop's
continuation. Secondary region-exits (early `return`/`throw`) are re-materialized
in place and read their loop values directly, so they are not scanned — and a
loop with no primary exit (`exit_dest === nothing`, e.g. an irreducible loop that
escapes only via early returns) has no escaping values at all. Values escape
through the continuation's exit-block phis, direct references downstream, or as
operands of a sequential loop.
"""
function find_extra_exit_values(ir::IRCode, loop_blocks::Set{Int},
                                 already_exported::Set{Int},
                                 exit_dest::Union{Int, Nothing})
    result = @NamedTuple{ssa_idx::Int, value::Any, type::Any}[]
    seen = Set{Int}()

    # Seed from the primary exit only; BFS its successors gives the post-loop
    # region where loop values may be read.
    reachable = Set{Int}()
    worklist = exit_dest === nothing ? Int[] : Int[exit_dest]
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
