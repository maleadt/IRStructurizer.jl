# CFGToSCF-style structurization
#
# Replaces the pattern-matching structural analysis with a principled two-phase
# algorithm inspired by MLIR's CFGToSCF (Bahmann et al. 2015):
#   Phase 1: Lift cycles to LoopOps (via natural loop detection)
#   Phase 2: Lift branches to IfOps (via dominance-based region splitting)
# Both phases are applied recursively until no unstructured CF remains.
# A post-pass promotes LoopOps to WhileOp/ForOp where possible.

using Graphs: SimpleDiGraph, add_edge!, strongly_connected_components

#=============================================================================
 Context
=============================================================================#

mutable struct StructurizeCtx
    ir::IRCode
    domtree::DomTree
    # header → set of block indices in the natural loop
    loop_map::Dict{Int, Set{Int}}
    next_ssa::Int
    next_arg::Int
    types::Vector{Any}
end

function StructurizeCtx(ir::IRCode)
    domtree = construct_domtree(ir)
    loops = compute_natural_loops(ir, domtree)
    n = length(ir.stmts.stmt)
    StructurizeCtx(ir, domtree, loops, n + 1, 1, copy(ir.stmts.type))
end

alloc_ssa!(ctx::StructurizeCtx) = (idx = ctx.next_ssa; ctx.next_ssa += 1; idx)
alloc_arg!(ctx::StructurizeCtx) = (id = ctx.next_arg; ctx.next_arg += 1; id)

#=============================================================================
 Natural Loop Detection
=============================================================================#

"""
    compute_natural_loops(ir, domtree) -> Dict{Int, Set{Int}}

Find all natural loops via backedge detection. A backedge src→header (where
header dominates src) defines a natural loop: header + all blocks that can
reach src without going through header.
"""
function compute_natural_loops(ir::IRCode, domtree::DomTree)
    loops = Dict{Int, Set{Int}}()
    for (i, bb) in enumerate(ir.cfg.blocks)
        for succ in bb.succs
            dominates(domtree, succ, i) || continue
            header = succ
            body = get!(Set{Int}, loops, header)
            push!(body, header)
            worklist = Int[i]
            while !isempty(worklist)
                b = pop!(worklist)
                b ∈ body && continue
                push!(body, b)
                for pred in ir.cfg.blocks[b].preds
                    pred ∉ body && push!(worklist, pred)
                end
            end
        end
    end
    loops
end

"""Return the innermost loop at `header` that is contained within `region_blocks`, or nothing."""
function get_loop_at(ctx::StructurizeCtx, header::Int, region_blocks::Set{Int})
    body = get(ctx.loop_map, header, nothing)
    body === nothing && return nothing
    # Only consider loops fully contained in the region
    issubset(body, region_blocks) || return nothing
    return body
end

#=============================================================================
 Entry Point
=============================================================================#

"""
    structurize(ir::IRCode) -> (Block, max_ssa, max_arg)

Convert flat IRCode into a structured Block with nested IfOp/LoopOp/WhileOp/ForOp.
"""
function structurize(ir::IRCode)
    ctx = StructurizeCtx(ir)
    all_blocks = Set(1:length(ir.cfg.blocks))
    entry = structurize_region!(ctx, 1, all_blocks)
    promote_loops!(entry, ctx)
    return entry, ctx.next_ssa - 1, ctx.next_arg - 1
end

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

    while current !== nothing && current ∈ region_blocks
        last_block = current

        # --- Loop header? (only if not already inside this loop) ---
        if loop_ctx === nothing || current != loop_ctx.header
            loop_body = get_loop_at(ctx, current, region_blocks)
            if loop_body !== nothing
                exit_dest = emit_loop!(block, ctx, current, loop_body, region_blocks)
                current = resolve_dest(exit_dest, region_blocks, loop_ctx, block)
                continue
            end
        end

        # --- Emit non-phi/non-terminator statements ---
        emit_block_stmts!(block, ctx, current)

        # --- Handle terminator ---
        term = find_terminator(ir, current)

        if term isa ReturnNode
            block.terminator = term
            return block
        elseif term isa GotoNode
            current = resolve_dest(term.label, region_blocks, loop_ctx, block)
        elseif term isa GotoIfNot
            next = emit_branch!(block, ctx, current, term, region_blocks, merge_phis, loop_ctx)
            if next === nothing
                return block
            end
            current = resolve_dest(next, region_blocks, loop_ctx, block)
        else
            # Fallthrough
            next = current + 1
            current = resolve_dest(next <= nblocks ? next : nothing,
                                    region_blocks, loop_ctx, block)
        end
    end

    # Region ended — set terminator if not already set
    if block.terminator === nothing && merge_phis !== nothing
        block.terminator = make_exit_yield(ir, merge_phis, last_block, block)
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

"""Emit non-phi, non-terminator statements from a basic block."""
function emit_block_stmts!(block::Block, ctx::StructurizeCtx, bb_idx::Int)
    ir = ctx.ir
    bb = ir.cfg.blocks[bb_idx]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        (stmt isa PhiNode || stmt isa GotoNode ||
         stmt isa GotoIfNot || stmt isa ReturnNode) && continue
        push!(block, si, stmt, ir.stmts.type[si])
    end
end

"""Find the terminator statement in a basic block."""
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
    true_dest = current + 1
    cond = gotoifnot.cond

    # Determine branch regions and merge block using dominance
    then_blocks, else_blocks, merge = find_branch_regions(
        ctx, current, true_dest, false_dest, region_blocks)

    # If merge exists and is in region, extract its phis.
    # Skip phis at loop headers — those are loop-carried values, not branch merge values.
    merge_phis = if merge !== nothing && merge ∈ region_blocks && !haskey(ctx.loop_map, merge)
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

    if merge !== nothing && merge ∈ region_blocks && merge_phis !== nothing
        # --- Inner merge exists: standard IfOp ---
        set_branch_yields!(then_blk, merge_phis, then_blocks, current, ir, block, ctx)
        set_branch_yields!(else_blk, merge_phis, else_blocks, current, ir, block, ctx)

        if_op = IfOp(cond, then_blk, else_blk)
        phi_indices = [p.ssa_idx for p in merge_phis]
        phi_types = [ctx.types[p.ssa_idx] for p in merge_phis]
        emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx)
        return merge
    elseif merge !== nothing && merge ∈ region_blocks
        # Merge exists but no phis
        set_yield_if_needed!(then_blk)
        set_yield_if_needed!(else_blk)
        if_op = IfOp(cond, then_blk, else_blk)
        push!(block, alloc_ssa!(ctx), if_op, Tuple{})
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
            # Create IfOp result with getfields, then yield them upward
            phi_indices = [p.ssa_idx for p in outer_merge_phis]
            phi_types = [ctx.types[p.ssa_idx] for p in outer_merge_phis]
            emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx)
            block.terminator = YieldOp(IRValue[SSAValue(idx) for idx in phi_indices])
        else
            push!(block, alloc_ssa!(ctx), if_op, Nothing)
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

"""Ensure a block has a terminator (YieldOp if nothing set)."""
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
    # Merge phis? Set yield for this edge.
    if merge_phis !== nothing && !isempty(merge_phis)
        b.terminator = make_yield_for_edge(ir, merge_phis, from, b, ctx)
    end
    return b
end

"""Find the block in `blocks` (or `fallback`) that is a predecessor of merge phis."""
function find_exit_predecessor(merge_phis::Vector{MergePhiInfo}, blocks::Set{Int},
                                fallback::Int, ir::IRCode)
    # Check merge phi edge values for a block in our set
    for phi in merge_phis
        for (pred, _) in phi.edge_values
            pred ∈ blocks && return pred
        end
    end
    # If branch is empty, the predecessor is the branch entry (fallback)
    return fallback
end

"""Create a YieldOp with values from merge phis for a given predecessor edge."""
function make_yield_for_edge(ir::IRCode, merge_phis::Vector{MergePhiInfo},
                              pred::Int, blk::Block, ctx::StructurizeCtx)
    yield_values = IRValue[]
    for phi in merge_phis
        val = get(phi.edge_values, pred, nothing)
        if val !== nothing
            # Check if the block already defines this SSA (from inner IfOp getfield)
            resolved = resolve_yield_value(blk, phi.ssa_idx, val)
            push!(yield_values, resolved)
        else
            push!(yield_values, Undef(ctx.types[phi.ssa_idx]))
        end
    end
    return YieldOp(yield_values)
end

"""Create a YieldOp for exiting a region at `last_block`."""
function make_exit_yield(ir::IRCode, merge_phis::Vector{MergePhiInfo},
                          last_block::Int, blk::Block)
    yield_values = IRValue[]
    for phi in merge_phis
        val = get(phi.edge_values, last_block, nothing)
        resolved = val !== nothing ? resolve_yield_value(blk, phi.ssa_idx, val) :
                                     Undef(ir.stmts.type[phi.ssa_idx])
        push!(yield_values, resolved)
    end
    return YieldOp(yield_values)
end

"""
If the block already defines `phi_ssa_idx` (e.g., via an inner IfOp's getfield),
yield SSAValue(phi_ssa_idx). Otherwise yield `default_val`.
"""
function resolve_yield_value(blk::Block, phi_ssa_idx::Int, default_val)
    haskey(blk.body, phi_ssa_idx) ? SSAValue(phi_ssa_idx) : default_val
end

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

    # Collect blocks dominated by each successor (if single-predecessor)
    if true_dest ∈ region_blocks && true_dest <= nblocks &&
       count(p -> p ∈ region_blocks, ir.cfg.blocks[true_dest].preds) == 1
        collect_dominated!(then_blocks, ctx.domtree, true_dest, region_blocks)
    end

    if false_dest ∈ region_blocks && false_dest <= nblocks &&
       count(p -> p ∈ region_blocks, ir.cfg.blocks[false_dest].preds) == 1
        collect_dominated!(else_blocks, ctx.domtree, false_dest, region_blocks)
    end

    # Remove any overlap with loop bodies that will be handled separately
    # (a block should only be in one region)
    setdiff!(then_blocks, else_blocks)

    # Merge = the first block reachable from both branches that's not in either.
    # It must be a successor of some block in then_blocks or else_blocks (or current),
    # and it must be dominated by `current` (not an unrelated earlier block).
    merge = nothing
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
    # Also check direct successors of current (for if-then patterns)
    if true_dest ∈ region_blocks && true_dest ∉ then_blocks
        push!(candidates, true_dest)
    end
    if false_dest ∈ region_blocks && false_dest ∉ else_blocks
        push!(candidates, false_dest)
    end

    # Prefer non-loop-header candidates: when a branch guards a loop entry,
    # the real merge is past the loop exit, not the loop header itself.
    sorted = sort!(collect(candidates))
    for c in sorted
        if c ∈ region_blocks && c ∉ then_blocks && c ∉ else_blocks &&
           !haskey(ctx.loop_map, c)
            merge = c
            break
        end
    end
    # Fallback to loop header if no better candidate
    if merge === nothing
        for c in sorted
            if c ∈ region_blocks && c ∉ then_blocks && c ∉ else_blocks
                merge = c
                break
            end
        end
    end

    return then_blocks, else_blocks, merge
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
    if !isempty(phi_indices)
        result_type = Tuple{phi_types...}
        push!(block, if_ssa, if_op, result_type)
        for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
            push!(block, phi_idx, Expr(:call, Core.getfield, SSAValue(if_ssa), i), phi_type)
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
    extra_exits = exit_dest !== nothing ?
        find_extra_exit_values(ir, exit_dest, loop_blocks, already_exported) :
        @NamedTuple{ssa_idx::Int, value::Any, type::Any}[]

    # 4. Build init/carried values and block arguments
    init_values = IRValue[]
    carried_values = IRValue[]
    phi_indices = Int[]
    phi_types = Any[]
    body = Block()
    subs = Dict{Int, BlockArgument}()

    for phi in phi_info
        push!(init_values, phi.entry_val)
        push!(carried_values, phi.carried_val)
        push!(phi_indices, phi.ssa_idx)
        push!(phi_types, ctx.types[phi.ssa_idx])
        arg = BlockArgument(alloc_arg!(ctx), ctx.types[phi.ssa_idx])
        push!(body.args, arg)
        subs[phi.ssa_idx] = arg
    end

    for ex in extra_exits
        push!(init_values, Undef(ex.type))
        push!(carried_values, ex.value)
        push!(phi_indices, ex.ssa_idx)
        push!(phi_types, ex.type)
        arg = BlockArgument(alloc_arg!(ctx), ex.type)
        push!(body.args, arg)
    end

    # 5. Find exit condition
    exit_info = find_loop_exit_condition(ir, loop_blocks)

    # 6. Build loop body
    build_loop_body!(body, ctx, header, loop_blocks, exit_info, carried_values, subs)

    # 7. Apply phi→arg substitutions
    sub_ctx = StructurizationContext(ctx.types, ctx.next_ssa, ctx.next_arg)
    apply_substitutions!(body, subs, sub_ctx)
    ctx.next_ssa = sub_ctx.next_value_idx
    ctx.next_arg = sub_ctx.next_arg_idx

    # 8. Emit LoopOp + getfields
    loop_op = LoopOp(body, init_values)
    loop_ssa = alloc_ssa!(ctx)
    result_type = Tuple{phi_types...}
    push!(block, loop_ssa, loop_op, result_type)

    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
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
                           loop_blocks::Set{Int}, exit_info, carried_values::Vector{IRValue},
                           subs::Dict{Int, BlockArgument})
    break_values = IRValue[arg for arg in body.args]
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

"""Find the entry to the loop body (successor of header that stays in the loop)."""
function find_loop_body_entry(ir::IRCode, header::Int, loop_blocks::Set{Int})
    for succ in ir.cfg.blocks[header].succs
        succ ∈ loop_blocks && succ != header && return succ
    end
    return nothing
end

"""
Find the GotoIfNot that controls loop exit.
Returns `(; cond, block, true_dest, false_dest, inverted)` or `nothing`.

`inverted=false`: cond=true → stay in loop, cond=false → exit
`inverted=true`: cond=true → exit, cond=false → stay in loop
"""
function find_loop_exit_condition(ir::IRCode, loop_blocks::Set{Int})
    nblocks = length(ir.cfg.blocks)
    for block_idx in loop_blocks
        bb = ir.cfg.blocks[block_idx]
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            stmt isa GotoIfNot || continue
            dest = stmt.dest
            fallthrough = block_idx + 1

            if dest ∉ loop_blocks
                return (; cond=stmt.cond, block=block_idx,
                         true_dest=fallthrough, false_dest=dest, inverted=false)
            elseif fallthrough <= nblocks && fallthrough ∉ loop_blocks
                return (; cond=stmt.cond, block=block_idx,
                         true_dest=fallthrough, false_dest=dest, inverted=true)
            end
        end
    end
    return nothing
end

"""Find loop-internal SSA values referenced outside the loop."""
function find_extra_exit_values(ir::IRCode, exit_dest::Int, loop_blocks::Set{Int},
                                 already_exported::Set{Int})
    result = @NamedTuple{ssa_idx::Int, value::Any, type::Any}[]
    nblocks = length(ir.cfg.blocks)
    seen = Set{Int}()

    for blk_idx in 1:nblocks
        blk_idx ∈ loop_blocks && continue
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
                        push!(result, (; ssa_idx=gf_idx, value=loop_val, type=ir.stmts.type[si]))
                        push!(seen, gf_idx)
                    end
                end
            else
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

#=============================================================================
 Loop Promotion (LoopOp → WhileOp / ForOp)
=============================================================================#

"""
Post-pass: walk the structured IR and promote LoopOps to WhileOp/ForOp
where the pattern matches.
"""
function promote_loops!(block::Block, ctx::StructurizeCtx)
    new_body = SSAMap()
    # Track ForOp promotions: loop_ssa_idx → (iv_pos, ForOp)
    for_promotions = Dict{Int, Tuple{Int, ForOp}}()

    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa LoopOp
            # Recursively promote inner loops first
            promote_loops!(stmt.body, ctx)
            # Try to promote this loop
            promoted = try_promote_while(stmt, ctx)
            if promoted !== nothing
                result, iv_pos = try_promote_for(promoted, idx, block, new_body, ctx)
                if result isa ForOp && iv_pos > 0
                    for_promotions[idx] = (iv_pos, result)
                    # Update result type: remove IV from tuple
                    carry_types = Any[]
                    for (i, t) in enumerate(entry.typ.parameters)
                        i == iv_pos && continue
                        push!(carry_types, t)
                    end
                    push!(new_body, (idx, result, Tuple{carry_types...}))
                else
                    push!(new_body, (idx, result, entry.typ))
                end
            else
                push!(new_body, (idx, stmt, entry.typ))
            end
        elseif stmt isa Expr && stmt.head === :call && stmt.args[1] === Core.getfield &&
               stmt.args[2] isa SSAValue && haskey(for_promotions, stmt.args[2].id)
            # Fix getfield for ForOp: IV position → upper bound, others → adjusted index
            loop_ssa = stmt.args[2].id
            field_idx = stmt.args[3]::Int
            iv_pos, for_op = for_promotions[loop_ssa]
            if field_idx == iv_pos
                # IV exit value = upper bound
                push!(new_body, (idx, for_op.upper, entry.typ))
            elseif field_idx > iv_pos
                # Adjust index (IV was removed from result tuple)
                new_gf = Expr(:call, Core.getfield, SSAValue(loop_ssa), field_idx - 1)
                push!(new_body, (idx, new_gf, entry.typ))
            else
                push!(new_body, (idx, stmt, entry.typ))
            end
        elseif stmt isa ControlFlowOp
            for b in blocks(stmt)
                promote_loops!(b, ctx)
            end
            push!(new_body, (idx, stmt, entry.typ))
        else
            push!(new_body, (idx, stmt, entry.typ))
        end
    end
    block.body = new_body
end

"""
Try to promote a LoopOp to WhileOp if the body has the form:
  header_stmts; IfOp(cond, then{...ContinueOp}, else{BreakOp})
"""
function try_promote_while(loop::LoopOp, ctx::StructurizeCtx)
    body = loop.body
    # The body should end with an IfOp (the last stmt)
    isempty(body.body) && return nothing

    last_idx = body.body.ssa_idxes[end]
    last_stmt = body.body.stmts[end]
    last_stmt isa IfOp || return nothing

    if_op = last_stmt

    # Determine which branch continues and which breaks
    then_term = if_op.then_region.terminator
    else_term = if_op.else_region.terminator

    is_then_continue = then_term isa ContinueOp
    is_else_break = else_term isa BreakOp
    is_then_break = then_term isa BreakOp
    is_else_continue = else_term isa ContinueOp

    if !(is_then_continue && is_else_break) && !(is_then_break && is_else_continue)
        return nothing
    end

    # The "stay" branch should have no other statements (just ContinueOp)
    # OR have body statements that form the loop body
    cond = if_op.condition
    stay_region = is_then_continue ? if_op.then_region : if_op.else_region
    exit_region = is_then_continue ? if_op.else_region : if_op.then_region

    # Negate condition if the "stay" branch is the else branch
    if is_else_continue
        # cond=true → break, cond=false → continue
        # WhileOp condition should be negated, but we can use the IfOp as-is
        # Actually for WhileOp: before checks condition, after is body
        # If cond=true → break, then while condition is NOT(cond)
        # We'll keep as LoopOp for now (promotion to WhileOp is complex with negation)
        # Only promote when cond=true → stay (standard while pattern)
        return nothing
    end

    # Standard pattern: cond=true → continue, cond=false → break
    # Build WhileOp: before = header stmts + ConditionOp, after = stay body + YieldOp

    continue_op = stay_region.terminator::ContinueOp

    # Guard: ContinueOp values must only reference block args or values defined
    # in the stay region. If they reference header SSAs (which go into `before`),
    # the WhileOp's `after` region can't see them — keep as LoopOp.
    for val in continue_op.values
        if val isa SSAValue && !haskey(stay_region.body, val.id)
            return nothing
        end
    end

    # Before region: header stmts (everything before the IfOp)
    before = Block()
    for (i, (sidx, sentry)) in enumerate(body.body)
        sidx == last_idx && break
        push!(before.body, (sidx, sentry.stmt, sentry.typ))
    end

    # Copy block args
    for arg in body.args
        push!(before.args, arg)
    end

    # ConditionOp args = before block args (passed to after region when cond is true)
    cond_args = IRValue[arg for arg in before.args]
    before.terminator = ConditionOp(cond, cond_args)

    # After region: stay_region body + YieldOp with carried values (back to before)
    after = Block()
    for arg in body.args
        after_arg = BlockArgument(alloc_arg!(ctx), arg.type)
        push!(after.args, after_arg)
    end
    for (sidx, sentry) in stay_region.body
        push!(after.body, (sidx, sentry.stmt, sentry.typ))
    end
    # YieldOp sends values back to before for the next iteration
    after.terminator = YieldOp(copy(continue_op.values))

    return WhileOp(before, after, loop.init_values)
end

"""
Try to promote a WhileOp to ForOp by detecting counting patterns.
Returns (promoted_op, iv_pos) where iv_pos > 0 if ForOp was created.
"""
function try_promote_for(op, idx::Int, parent_block::Block, new_body::SSAMap,
                          ctx::StructurizeCtx)
    op isa WhileOp || return (op, 0)

    # Look for: condition is slt_int/sle_int/=== on a block arg vs loop-invariant bound
    before = op.before
    before.terminator isa ConditionOp || return (op, 0)
    cond_op = before.terminator

    # Find the condition expression
    cond_val = cond_op.condition
    cond_val isa SSAValue || return (op, 0)
    cond_entry = get(before.body, cond_val.id, nothing)
    cond_entry === nothing && return (op, 0)
    cond_expr = cond_entry.stmt
    cond_expr isa Expr && cond_expr.head === :call || return (op, 0)
    length(cond_expr.args) >= 3 || return (op, 0)

    func = cond_expr.args[1]
    iv_candidate = cond_expr.args[2]
    bound = cond_expr.args[3]

    # Check condition function
    is_slt = func isa GlobalRef && func.name in (:slt_int, :ult_int)
    is_sle = func isa GlobalRef && func.name === :sle_int
    is_eq = (func isa GlobalRef && func.name === :(===)) || func === :(===)
    (is_slt || is_sle || is_eq) || return (op, 0)

    # IV must be a block argument
    iv_candidate isa BlockArgument || return (op, 0)

    # Find IV's position in args
    iv_pos = findfirst(a -> a.id == iv_candidate.id, before.args)
    iv_pos === nothing && return (op, 0)

    # Find step: look in the after region for add_int(iv_arg, step)
    after = op.after
    iv_pos <= length(after.args) || return (op, 0)
    after_iv_arg = after.args[iv_pos]
    before_iv_arg = before.args[iv_pos]

    # Find add_int in after body or in YieldOp values
    step = nothing
    carried_val = after.terminator isa YieldOp && iv_pos <= length(after.terminator.values) ?
        after.terminator.values[iv_pos] : nothing
    if carried_val isa SSAValue
        step_entry = get(after.body, carried_val.id, nothing)
        if step_entry !== nothing
            s = step_entry.stmt
            if s isa Expr && s.head === :call && length(s.args) >= 3
                sfunc = s.args[1]
                if sfunc isa GlobalRef && sfunc.name === :add_int
                    # Match either after or before block arg (cross-scope reference)
                    if s.args[2] isa BlockArgument &&
                       (s.args[2].id == after_iv_arg.id || s.args[2].id == before_iv_arg.id)
                        step = s.args[3]
                    end
                end
            end
        end
    end
    step === nothing && return (op, 0)

    # Bound must be loop-invariant (not a block arg of this loop)
    if bound isa BlockArgument && any(a -> a.id == bound.id, before.args)
        return (op, 0)
    end

    # Build ForOp
    lower = op.init_values[iv_pos]
    upper = bound
    is_inclusive = is_sle || is_eq

    # Exclusive upper bound: add 1 if inclusive
    if is_inclusive
        adj_ssa = alloc_ssa!(ctx)
        upper_type = iv_candidate.type
        add_expr = Expr(:call, GlobalRef(Base, :add_int), upper, one(upper_type))
        push!(new_body, (adj_ssa, add_expr, upper_type))
        upper = SSAValue(adj_ssa)
    end

    # Non-IV init values and body
    non_iv_inits = IRValue[]
    for (i, v) in enumerate(op.init_values)
        i == iv_pos && continue
        push!(non_iv_inits, v)
    end

    iv_arg = BlockArgument(alloc_arg!(ctx), iv_candidate.type)

    # Build ForOp body: copy after region, remove IV increment, adjust args
    for_body = Block()
    for (i, arg) in enumerate(after.args)
        i == iv_pos && continue
        push!(for_body.args, BlockArgument(alloc_arg!(ctx), arg.type))
    end

    for (sidx, sentry) in after.body
        # Skip the IV increment statement
        if carried_val isa SSAValue && sidx == carried_val.id
            continue
        end
        push!(for_body.body, (sidx, sentry.stmt, sentry.typ))
    end

    # ContinueOp with non-IV carried values
    cont_values = IRValue[]
    if after.terminator isa YieldOp
        for (i, v) in enumerate(after.terminator.values)
            i == iv_pos && continue
            push!(cont_values, v)
        end
    end
    for_body.terminator = ContinueOp(cont_values)

    return (ForOp(lower, upper, step, iv_arg, for_body, non_iv_inits), iv_pos)
end

#=============================================================================
 Compatibility shim for StructurizationContext
=============================================================================#

# Bridge between StructurizeCtx and StructurizationContext used by apply_substitutions!
function StructurizationContext(ctx::StructurizeCtx)
    StructurizationContext(ctx.types, ctx.next_ssa, ctx.next_arg)
end
