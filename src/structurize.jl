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
                # Update last_block to the loop's exit predecessor (for merge phi lookup)
                if exit_dest !== nothing
                    for b in loop_body
                        exit_dest ∈ ir.cfg.blocks[b].succs && (last_block = b)
                    end
                end
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
        block.terminator = make_exit_yield(ir, merge_phis, last_block, block, ctx)
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
    # Merge phis? Use reachability from dest to find the right phi edge value.
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

    # Check seeds directly
    for b in seeds, phi in merge_phis
        haskey(phi.edge_values, b) && return b
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
                          last_block::Int, blk::Block, ctx::StructurizeCtx)
    # Reuse find_exit_predecessor's BFS to find the right phi edge
    pred = find_exit_predecessor(merge_phis, Set{Int}([last_block]), last_block, ir)
    return make_yield_for_edge(ir, merge_phis, pred, blk, ctx)
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

    for c in sort!(collect(candidates))
        if c ∈ region_blocks && c ∉ then_blocks && c ∉ else_blocks
            merge = c
            break
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

StructurizationContext(ctx::StructurizeCtx) =
    StructurizationContext(ctx.types, ctx.next_ssa, ctx.next_arg)
