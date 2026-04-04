#=============================================================================
 Branch Region Splitting (dominance-based)
=============================================================================#

"""
    find_branch_regions(ctx, current, true_dest, false_dest, region_blocks)
        -> (then_blocks, else_blocks, merge)

Split region_blocks into then/else regions using dominance.
A successor with a single predecessor gets all blocks it dominates.
A successor with multiple predecessors is a merge block (empty region).
"""
function find_branch_regions(ctx::StructurizeCtx, current::Int,
                              true_dest::Int, false_dest::Int,
                              region_blocks::Set{Int})
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

    # Merge = the block where all paths from `current` reconverge.
    # Prefer the immediate post-dominator (structurally exact).
    # Fall back to successor-candidate search when early returns prevent
    # real post-dominance (ipdom = 0 = virtual exit).
    merge = nothing
    ipdom = ctx.postdomtree.idoms_bb[current]
    if ipdom != 0 && ipdom ∈ region_blocks && ipdom ∉ then_blocks && ipdom ∉ else_blocks
        merge = ipdom
    else
        candidates = Set{Int}()
        for b in then_blocks
            for s in ir.cfg.blocks[b].succs
                s ∉ then_blocks && s != current && push!(candidates, s)
            end
        end
        for b in else_blocks
            for s in ir.cfg.blocks[b].succs
                s ∉ else_blocks && s != current && push!(candidates, s)
            end
        end
        if true_dest ∈ region_blocks && true_dest ∉ then_blocks
            push!(candidates, true_dest)
        end
        if false_dest ∈ region_blocks && false_dest ∉ else_blocks
            push!(candidates, false_dest)
        end
        for c in sort!(collect(candidates))
            if c ∈ region_blocks && c ∉ then_blocks && c ∉ else_blocks
                merge = c
                break
            end
        end
    end

    return then_blocks, else_blocks, merge
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

"""Push an IfOp and generate getfield statements at each phi index."""
function emit_ifop_result!(block::Block, if_op::IfOp, phi_indices::Vector{Int},
                            phi_types::AbstractVector, ctx::StructurizeCtx)
    if_ssa = alloc_ssa!(ctx)
    remap = ctx.ssa_remap
    if !isempty(phi_indices)
        result_type = Tuple{phi_types...}
        push!(block, if_ssa, if_op, result_type)
        for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
            idx = get(remap, phi_idx, phi_idx)
            push!(block, idx, Expr(:call, Core.getfield, SSAValue(if_ssa), i), phi_type)
        end
    else
        push!(block, if_ssa, if_op, Tuple{})
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

    # 2. Find exit destination
    exit_dest = find_loop_exit(ir, loop_blocks)

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
        push!(init_values, Undef(ex.type))
        push!(carried_values, SSAValue(fresh))  # carry the fresh-index value
        push!(phi_indices, ex.ssa_idx)           # getfield OUTSIDE uses original
        push!(phi_types, ex.type)
        arg = BlockArgument(alloc_arg!(ctx), ex.type)
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
    loop_op = LoopOp(body, init_values)
    loop_ssa = alloc_ssa!(ctx)
    result_type = Tuple{phi_types...}
    push!(block, loop_ssa, loop_op, result_type)

    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
        # If a preceding IfOp already defined this phi SSA (multi-entry header),
        # use a fresh index for the loop's getfield to avoid SSA uniqueness violation.
        # Downstream code references phi_idx which is the IfOp's definition;
        # the loop result is accessed via the fresh index (only used if phi changes in loop).
        idx = haskey(block.body, phi_idx) ? alloc_ssa!(ctx) : phi_idx
        push!(block, idx, Expr(:call, Core.getfield, SSAValue(loop_ssa), i), phi_type)
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

"""Merge the content of `src` into `dst` (body + terminator)."""
function merge_block_into!(dst::Block, src::Block)
    for (idx, entry) in src.body
        push!(dst.body, (idx, entry.stmt, entry.typ))
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

"""Find the block index that the loop exits to (first successor outside loop_blocks)."""
function find_loop_exit(ir::IRCode, loop_blocks::Set{Int})
    for b in loop_blocks
        for succ in ir.cfg.blocks[b].succs
            succ ∉ loop_blocks && return succ
        end
    end
    return nothing
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

    # Collect all non-loop blocks reachable from loop exit edges
    reachable = Set{Int}()
    worklist = Int[]
    for b in loop_blocks
        for succ in ir.cfg.blocks[b].succs
            succ ∉ loop_blocks && push!(worklist, succ)
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

function stmt_ssa_uses(stmt)
    if stmt isa Expr
        return Iterators.filter(x -> x isa SSAValue, stmt.args)
    elseif stmt isa GotoIfNot && stmt.cond isa SSAValue
        return (stmt.cond,)
    elseif stmt isa ReturnNode && isdefined(stmt, :val) && stmt.val isa SSAValue
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
