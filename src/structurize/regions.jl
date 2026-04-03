# Control tree to structured IR: entry point and region handlers

#=============================================================================
 Control Tree to Structured IR
=============================================================================#

"""
    control_tree_to_structured_ir(ctree::ControlTree, ir::IRCode, ctx::StructurizationContext) -> Block

Convert a control tree to structured IR entry block.
All loops become LoopOp (no pattern matching yet, no substitutions).
"""
function control_tree_to_structured_ir(ctree::ControlTree, ir::IRCode,
                                       ctx::StructurizationContext)
    return tree_to_block(ctree, ir, ctx)
end

"""
    tree_to_block(tree::ControlTree, ir::IRCode, ctx::StructurizationContext) -> Block

Convert a control tree node to a Block with raw expressions (no substitutions).
"""
function tree_to_block(tree::ControlTree, ir::IRCode, ctx::StructurizationContext)
    idx = node_index(tree)
    rtype = region_type(tree)
    block = Block()

    if rtype == REGION_BLOCK
        handle_block_region!(block, tree, ir, ctx)
    elseif rtype == REGION_IF_THEN_ELSE
        handle_if_then_else!(block, tree, ir, ctx)
    elseif rtype == REGION_IF_THEN
        handle_if_then!(block, tree, ir, ctx)
    elseif rtype == REGION_TERMINATION
        handle_termination!(block, tree, ir, ctx)
    elseif rtype == REGION_FOR_LOOP || rtype == REGION_WHILE_LOOP || rtype == REGION_NATURAL_LOOP
        handle_loop!(block, tree, ir, ctx)
    elseif rtype == REGION_PROPER
        handle_proper_region!(block, tree, ir, ctx)
    else
        error("Unknown region type: $rtype")
    end

    # Set terminator if not already set
    set_block_terminator!(block, ir)

    return block
end

#=============================================================================
 Region Handlers
=============================================================================#

"""
    handle_block_region!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_BLOCK - a linear sequence of blocks.
"""
function handle_block_region!(block::Block, tree::ControlTree, ir::IRCode,
                              ctx::StructurizationContext)
    nblocks = length(ir.cfg.blocks)
    if isempty(children(tree))
        # Leaf node - collect statements from the block
        idx = node_index(tree)
        if 1 <= idx <= nblocks
            collect_block_statements!(block, idx, ir)
        end
    else
        # Non-leaf - process children in order
        for child in children(tree)
            child_rtype = region_type(child)
            if child_rtype == REGION_BLOCK
                handle_block_region!(block, child, ir, ctx)
            else
                # Nested control flow - create appropriate op
                handle_nested_region!(block, child, ir, ctx)
            end
        end
    end
end

"""
    handle_nested_region!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle a nested control flow region.
"""
function handle_nested_region!(block::Block, tree::ControlTree, ir::IRCode,
                               ctx::StructurizationContext)
    rtype = region_type(tree)

    if rtype == REGION_IF_THEN_ELSE
        handle_if_then_else!(block, tree, ir, ctx)
    elseif rtype == REGION_IF_THEN
        handle_if_then!(block, tree, ir, ctx)
    elseif rtype == REGION_TERMINATION
        handle_termination!(block, tree, ir, ctx)
    elseif rtype == REGION_FOR_LOOP || rtype == REGION_WHILE_LOOP || rtype == REGION_NATURAL_LOOP
        handle_loop!(block, tree, ir, ctx)
    elseif rtype == REGION_PROPER
        handle_proper_region!(block, tree, ir, ctx)
    else
        error("Unknown region type in nested region: $rtype")
    end
end

"""
    resolve_yield(blk, phi_ssa_idx, default_val)

If `blk` already defines `phi_ssa_idx` (e.g., via an inner IfOp's getfield for nested
short-circuit patterns), yield SSAValue(phi_ssa_idx). Otherwise yield `default_val`.
"""
function resolve_yield(blk::Block, phi_ssa_idx::Int, default_val)
    get(blk.body, phi_ssa_idx, nothing) !== nothing ? SSAValue(phi_ssa_idx) : default_val
end

"""
    emit_ifop_result!(block, if_op, phi_ssa_indices, phi_types, ctx) -> Int

Push an IfOp to `block` with its result type, then generate getfield statements at
each `phi_ssa_indices[i]`. Returns the IfOp's SSA index.

Used by `emit_if_op!`, `handle_proper_region!`, and `build_proper_branch!` to avoid
repeating the IfOp allocation / getfield pattern.
"""
function emit_ifop_result!(block::Block, if_op::IfOp, phi_ssa_indices::Vector{Int},
                            phi_types::Vector{Any}, ctx::StructurizationContext)
    if_result_idx = ctx.next_value_idx
    ctx.next_value_idx += 1

    if !isempty(phi_ssa_indices)
        result_type = Tuple{phi_types...}
        push!(block, if_result_idx, if_op, result_type)

        for (i, (phi_idx, phi_type)) in enumerate(zip(phi_ssa_indices, phi_types))
            getfield_expr = Expr(:call, Core.getfield, SSAValue(if_result_idx), i)
            push!(block, phi_idx, getfield_expr, phi_type)
        end
    else
        push!(block, if_result_idx, if_op, Tuple{})
    end

    return if_result_idx
end

"""
    emit_if_op!(block, cond_idx, then_tree, else_tree_or_nothing, ir, ctx; is_termination=false)

Unified handler for if-like regions (IF_THEN_ELSE, IF_THEN, TERMINATION).

- For IF_THEN_ELSE: pass both then_tree and else_tree
- For IF_THEN: pass else_tree=nothing (creates empty else block, uses cond_idx as else proxy)
- For TERMINATION: pass is_termination=true (preserves return terminators, Nothing result type)
"""
function emit_if_op!(block::Block, cond_idx::Int,
                      then_tree::ControlTree, else_tree::Union{ControlTree,Nothing},
                      ir::IRCode, ctx::StructurizationContext;
                      is_termination::Bool=false)
    emit_condition_block_stmts!(block, cond_idx, ir)
    cond_value = find_condition_value(cond_idx, ir)

    then_blk = tree_to_block(then_tree, ir, ctx)
    else_blk = else_tree !== nothing ? tree_to_block(else_tree, ir, ctx) : Block()

    if is_termination
        then_blk.terminator = something(then_blk.terminator, YieldOp())
        else_blk.terminator = something(else_blk.terminator, YieldOp())
        if_op = IfOp(cond_value, then_blk, else_blk)

        # Use gotoifnot SSA index as result key
        nblocks = length(ir.cfg.blocks)
        bb = ir.cfg.blocks[cond_idx]
        result_idx = last(bb.stmts)
        for si in first(bb.stmts):last(bb.stmts)
            ir.stmts.stmt[si] isa GotoIfNot && (result_idx = si; break)
        end
        push!(block, result_idx, if_op, Nothing)
    else
        # Find merge phis
        then_rblocks = get_region_blocks(then_tree, ir)
        then_exit = get_exit_block(then_tree, ir, then_rblocks)

        else_rblocks = else_tree !== nothing ?
            get_region_blocks(else_tree, ir) : Set{Int}((cond_idx,))
        else_exit = else_tree !== nothing ?
            get_exit_block(else_tree, ir, else_rblocks) : cond_idx

        merge_phis = find_merge_phis(ir, then_exit, else_exit;
                                      then_blocks=then_rblocks,
                                      else_blocks=else_rblocks)

        then_blk.terminator, else_blk.terminator = if !isempty(merge_phis)
            # If a branch already defines the merge phi's SSA index (e.g., via an inner
            # IfOp's getfield for nested short-circuit patterns like &&), yield that
            # SSAValue instead of the raw phi edge value from find_merge_phis.
            YieldOp([resolve_yield(then_blk, phi.ssa_idx, phi.then_val) for phi in merge_phis]),
            YieldOp([resolve_yield(else_blk, phi.ssa_idx, phi.else_val) for phi in merge_phis])
        else
            something(then_blk.terminator, YieldOp()),
            something(else_blk.terminator, YieldOp())
        end

        if_op = IfOp(cond_value, then_blk, else_blk)
        phi_indices = Int[phi.ssa_idx for phi in merge_phis]
        phi_types = Any[ctx.ssavaluetypes[phi.ssa_idx] for phi in merge_phis]
        emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx)
    end
end

"""
    handle_if_then_else!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_IF_THEN_ELSE.
"""
function handle_if_then_else!(block::Block, tree::ControlTree, ir::IRCode,
                              ctx::StructurizationContext)
    tree_children = children(tree)
    length(tree_children) >= 3 || return handle_block_region!(block, tree, ir, ctx)
    cond_idx = node_index(tree_children[1])
    emit_if_op!(block, cond_idx, tree_children[2], tree_children[3], ir, ctx)
end

"""
    is_defined_in_blocks(val, blocks::Set{Int}, ir::IRCode) -> Bool

Check if an SSAValue's definition falls within any of the given blocks' stmt ranges.
Non-SSAValue values (constants, Arguments) are always considered "not block-local".
"""
function is_defined_in_blocks(val, blocks::Set{Int}, ir::IRCode)
    val isa SSAValue || return false
    nblocks = length(ir.cfg.blocks)
    for block_idx in blocks
        1 <= block_idx <= nblocks || continue
        bb = ir.cfg.blocks[block_idx]
        if val.id in first(bb.stmts):last(bb.stmts)
            return true
        end
    end
    return false
end

"""
    find_extra_exit_values(ir, exit_dest, loop_blocks, already_exported) -> Vector{NamedTuple}

Find loop-internal values referenced outside the loop that are not already
exported via header phis. Returns a vector of `(; value, getfield_idx, type)` tuples.

Scans ALL blocks outside the loop (not just the exit target) because loop-internal
values may be referenced in blocks far beyond the immediate exit — e.g., when two
sequential for-loops share an accumulator.
"""
function find_extra_exit_values(ir::IRCode, exit_dest::Int, loop_blocks::Set{Int},
                                already_exported::Set{Int})
    extra = @NamedTuple{value::IRValue, getfield_idx::Int, type::Any}[]
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    nblocks = length(ir.cfg.blocks)
    1 <= exit_dest <= nblocks || return extra

    seen = Set{Int}()  # track getfield_idx to avoid duplicates

    for blk_idx in 1:nblocks
        blk_idx ∈ loop_blocks && continue
        bb = ir.cfg.blocks[blk_idx]

        for si in first(bb.stmts):last(bb.stmts)
            stmt = stmts[si]

            if stmt isa PhiNode
                si ∈ already_exported && continue

                # Find value from loop blocks
                loop_val = nothing
                for (edge_idx, edge) in enumerate(stmt.edges)
                    if isassigned(stmt.values, edge_idx) && edge ∈ loop_blocks
                        loop_val = stmt.values[edge_idx]
                    end
                end

                if loop_val !== nothing
                    gf_idx = loop_val isa SSAValue ? loop_val.id : si
                    gf_idx ∈ seen && continue
                    push!(extra, (; value=loop_val, getfield_idx=gf_idx, type=types[si]))
                    push!(seen, gf_idx)
                end
            else
                # Check all SSAValue references in statements outside the loop
                for arg in _stmt_ssa_uses(stmt)
                    if is_defined_in_blocks(arg, loop_blocks, ir)
                        arg.id ∈ already_exported && continue
                        arg.id ∈ seen && continue
                        push!(extra, (; value=arg, getfield_idx=arg.id, type=types[arg.id]))
                        push!(seen, arg.id)
                    end
                end
            end
        end
    end

    return extra
end

"""
    _stmt_ssa_uses(stmt) -> iterator of SSAValue

Extract all SSAValue references from a statement (Expr args, GotoIfNot cond,
ReturnNode val, PhiNode values are handled separately).
"""
function _stmt_ssa_uses(stmt)
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

"""
    pad_extra_exits!(extra_exits, init_values, carried_values, body, phi_indices, phi_types, ctx)

Pad extra exit values into the loop-carry chain and append to phi tracking vectors.
Each extra exit value becomes a loop-carried variable with `Undef` initial value.
"""
function pad_extra_exits!(extra_exits, init_values, carried_values, body, phi_indices, phi_types, ctx::StructurizationContext)
    for (j, ex) in enumerate(extra_exits)
        push!(init_values, Undef(ex.type))
        push!(carried_values, ex.value)
        id = alloc_arg_id!(ctx)
        push!(body.args, BlockArgument(id, ex.type))
    end
    for ex in extra_exits
        push!(phi_indices, ex.getfield_idx)
        push!(phi_types, ex.type)
    end
end

"""
    find_merge_phis(ir, then_block_idx, else_block_idx; then_blocks, else_blocks)

Find phis in the merge block (common successor of then and else blocks)
that receive values from both branches.

When a phi has only one incoming edge and the value is branch-local (defined
within that branch's blocks), `Undef(T)` is used for the dead branch instead
of duplicating the branch-local SSAValue.

Returns a vector of NamedTuples: (ssa_idx, then_val, else_val)
"""
function find_merge_phis(ir::IRCode, then_block_idx::Int, else_block_idx::Int;
                         then_blocks::Set{Int}=Set{Int}(), else_blocks::Set{Int}=Set{Int}())
    merge_phis = NamedTuple{(:ssa_idx, :then_val, :else_val), Tuple{Int, Any, Any}}[]
    nblocks = length(ir.cfg.blocks)

    # Find common successor (merge block)
    then_succs = 1 <= then_block_idx <= nblocks ? ir.cfg.blocks[then_block_idx].succs : Int[]
    else_succs = 1 <= else_block_idx <= nblocks ? ir.cfg.blocks[else_block_idx].succs : Int[]
    merge_blocks = intersect(then_succs, else_succs)
    isempty(merge_blocks) && return merge_phis

    merge_block_idx = first(merge_blocks)
    1 <= merge_block_idx <= nblocks || return merge_phis
    merge_bb = ir.cfg.blocks[merge_block_idx]

    # Look for phis that have edges from both then and else blocks
    # In IRCode, phi edges are BLOCK indices directly
    for si in first(merge_bb.stmts):last(merge_bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa PhiNode || continue

        then_val = nothing
        else_val = nothing
        for (edge_idx, edge) in enumerate(stmt.edges)
            # edge is a block index in IRCode
            if edge == then_block_idx
                then_val = stmt.values[edge_idx]
            elseif edge == else_block_idx
                else_val = stmt.values[edge_idx]
            end
        end

        # Include phis with values from at least one branch.
        # In SSA form, a phi with only one incoming edge means the value is live on that
        # path alone. A structured IfOp must yield equal arity from both branches.
        if then_val !== nothing && else_val !== nothing
            push!(merge_phis, (ssa_idx=si, then_val=then_val, else_val=else_val))
        elseif then_val !== nothing
            # Only then branch has a value. If branch-local, the other path gets Undef
            # (the value is dead there, guarded by the branch condition).
            if is_defined_in_blocks(then_val, then_blocks, ir)
                push!(merge_phis, (ssa_idx=si, then_val=then_val, else_val=Undef(ir.stmts.type[si])))
            else
                # Value is visible in both scopes (e.g., Argument, constant, or outer SSA)
                push!(merge_phis, (ssa_idx=si, then_val=then_val, else_val=then_val))
            end
        elseif else_val !== nothing
            if is_defined_in_blocks(else_val, else_blocks, ir)
                push!(merge_phis, (ssa_idx=si, then_val=Undef(ir.stmts.type[si]), else_val=else_val))
            else
                push!(merge_phis, (ssa_idx=si, then_val=else_val, else_val=else_val))
            end
        end
    end

    return merge_phis
end

"""
    handle_if_then!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_IF_THEN.
"""
function handle_if_then!(block::Block, tree::ControlTree, ir::IRCode,
                         ctx::StructurizationContext)
    tree_children = children(tree)
    length(tree_children) >= 2 || return handle_block_region!(block, tree, ir, ctx)
    cond_idx = node_index(tree_children[1])
    emit_if_op!(block, cond_idx, tree_children[2], nothing, ir, ctx)
end

"""
    handle_termination!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_TERMINATION - branches where some paths terminate.
"""
function handle_termination!(block::Block, tree::ControlTree, ir::IRCode,
                             ctx::StructurizationContext)
    tree_children = children(tree)
    isempty(tree_children) && return handle_block_region!(block, tree, ir, ctx)
    cond_idx = node_index(tree_children[1])

    if length(tree_children) >= 3
        emit_if_op!(block, cond_idx, tree_children[2], tree_children[3], ir, ctx;
                     is_termination=true)
    elseif length(tree_children) == 2
        emit_if_op!(block, cond_idx, tree_children[2], nothing, ir, ctx;
                     is_termination=true)
    end
end

"""
    handle_loop!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_FOR_LOOP, REGION_WHILE_LOOP, and REGION_NATURAL_LOOP.

For REGION_FOR_LOOP: Creates ForOp directly using metadata from CFG analysis.
For REGION_WHILE_LOOP: Creates WhileOp directly with before/after regions.
For REGION_NATURAL_LOOP: Creates LoopOp with internal IfOp (fallback for complex loops).

The loop is keyed at a synthesized SSA index, and getfield statements are generated
at the original phi node indices. This ensures that references like `return %2`
continue to work because getfield is placed at %2.
"""
function handle_loop!(block::Block, tree::ControlTree, ir::IRCode,
                      ctx::StructurizationContext)
    rtype = region_type(tree)

    # Dispatch based on region type
    post_loop_blocks = Int[]
    if rtype == REGION_FOR_LOOP
        loop_op, phi_indices, phi_types = build_for_op(block, tree, ir, ctx)
    elseif rtype == REGION_WHILE_LOOP
        loop_op, phi_indices, phi_types = build_while_op(tree, ir, ctx)
    else  # REGION_NATURAL_LOOP or other cyclic regions
        loop_op, phi_indices, phi_types, post_loop_blocks = build_loop_op(tree, ir, ctx)
    end

    # Allocate new SSA index for loop's tuple result
    loop_result_idx = ctx.next_value_idx
    ctx.next_value_idx += 1

    # Always use Tuple type for loop results (uniform handling in codegen)
    # Empty phi_indices produces Tuple{} which is fine
    result_type = Tuple{phi_types...}

    # Push loop op at synthesized index
    push!(block, loop_result_idx, loop_op, result_type)

    # Generate getfield statements at original phi indices
    # This preserves SSA reference semantics: `return %2` still works because getfield is at %2
    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
        getfield_expr = Expr(:call, Core.getfield, SSAValue(loop_result_idx), i)
        push!(block, phi_idx, getfield_expr, phi_type)
    end

    # For ForOp, the IV phi is excluded from phi_indices but may still be referenced.
    # Define it as the exclusive upper bound (the IV's value at loop exit).
    if rtype == REGION_FOR_LOOP
        for_info = metadata(tree)::ForLoopInfo
        iv_phi_idx = for_info.iv_phi_idx
        iv_type = ctx.ssavaluetypes[iv_phi_idx]
        push!(block, iv_phi_idx, loop_op.upper, iv_type)
    end

    # Emit post-loop content: children that were in the control tree but outside
    # the natural loop (e.g., exit-target subtrees absorbed by TERMINATION regions).
    # These are processed as full structured regions, not flattened blocks,
    # because they may contain loops or other complex control flow.
    for child in post_loop_blocks
        process_child_region!(block, child, ir, ctx)
    end
end

"""
    handle_proper_region!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_PROPER — a multi-exit acyclic region (e.g., short-circuit `||`/`&&`).

Lowers to nested IfOps by tracing each path from entry to the merge block.
The merge block may be inside the region (e.g., `||`) or outside it (e.g., `&&`);
both cases are handled.
"""
function handle_proper_region!(block::Block, tree::ControlTree, ir::IRCode,
                                ctx::StructurizationContext)
    tree_children = children(tree)
    isempty(tree_children) && return handle_block_region!(block, tree, ir, ctx)

    nblocks = length(ir.cfg.blocks)
    entry_idx = node_index(tree_children[1])
    1 <= entry_idx <= nblocks || return handle_block_region!(block, tree, ir, ctx)

    # Verify entry block has a GotoIfNot
    bb = ir.cfg.blocks[entry_idx]
    gotoifnot = nothing
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa GotoIfNot && (gotoifnot = stmt; break)
    end
    gotoifnot === nothing && return handle_block_region!(block, tree, ir, ctx)

    region_blocks = get_region_blocks(tree, ir)

    # Find merge block: a block with phi nodes having ≥2 edges from region blocks.
    # Try inside the region first (e.g., `||`), then outside (e.g., `&&`).
    merge_idx = find_proper_merge_block(region_blocks, ir, nblocks)
    merge_idx === nothing && return handle_block_region!(block, tree, ir, ctx)
    merge_is_internal = merge_idx in region_blocks

    # Collect merge phi information: for each phi, map predecessor block → value
    merge_phis = collect_proper_merge_phis(merge_idx, region_blocks, ir)

    # Emit entry block statements (excluding control flow and phis)
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        if !(stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode || stmt isa PhiNode)
            push!(block, si, stmt, ir.stmts.type[si])
        end
    end

    cond_value = find_condition_value(entry_idx, ir)

    # GotoIfNot: condition false → dest, condition true → fallthrough
    false_target = gotoifnot.dest
    true_target = nothing
    for succ in ir.cfg.blocks[entry_idx].succs
        succ != false_target && (true_target = succ; break)
    end

    # Build mapping from block index → control tree child for non-leaf sub-trees.
    # When build_proper_branch! encounters such a block, it processes the sub-tree
    # via tree_to_block instead of walking raw IR blocks.
    subtree_map = Dict{Int, ControlTree}()
    for child in tree_children
        if !isempty(children(child))
            subtree_map[node_index(child)] = child
        end
    end

    # Build then and else branches recursively
    then_blk = Block()
    else_blk = Block()
    build_proper_branch!(then_blk, true_target, entry_idx, merge_idx, merge_phis,
                          region_blocks, ir, ctx, subtree_map)
    build_proper_branch!(else_blk, false_target, entry_idx, merge_idx, merge_phis,
                          region_blocks, ir, ctx, subtree_map)

    # Emit IfOp with merge phi results
    if_op = IfOp(cond_value, then_blk, else_blk)
    phi_indices = Int[phi.ssa_idx for phi in merge_phis]
    phi_types = Any[ctx.ssavaluetypes[phi.ssa_idx] for phi in merge_phis]
    emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx)

    # If merge block is inside the region, process its content here.
    # When the merge block is the root of a control tree subtree (e.g., a
    # TERMINATION region with further if/return chains), we must process
    # the full subtree — not just the raw statements — to preserve the
    # downstream control flow.
    if merge_is_internal
        merge_subtree = get(subtree_map, merge_idx, nothing)
        if merge_subtree !== nothing
            handle_nested_region!(block, merge_subtree, ir, ctx)
        else
            merge_bb = ir.cfg.blocks[merge_idx]
            for si in first(merge_bb.stmts):last(merge_bb.stmts)
                stmt = ir.stmts.stmt[si]
                if stmt isa ReturnNode
                    block.terminator = stmt
                elseif !(stmt isa PhiNode || stmt isa GotoNode || stmt isa GotoIfNot)
                    push!(block, si, stmt, ir.stmts.type[si])
                end
            end
        end
    end
end

"""
    find_proper_merge_block(region_blocks, ir, nblocks) -> Union{Int, Nothing}

Find the merge block for a proper region: a block with phi nodes having ≥2 edges
from region blocks. Searches both inside (e.g., `||`) and outside (e.g., `&&`).
"""
function find_proper_merge_block(region_blocks::Set{Int}, ir::IRCode, nblocks::Int)
    # Collect candidates: internal blocks (reverse-sorted, merge is typically last in RPO)
    # plus external successor blocks.
    candidates = sort!(collect(region_blocks); rev=true)
    for b in region_blocks
        1 <= b <= nblocks || continue
        for succ in ir.cfg.blocks[b].succs
            succ in region_blocks || push!(candidates, succ)
        end
    end

    # Single pass: find first block with a phi having ≥2 edges from region blocks
    for idx in candidates
        1 <= idx <= nblocks || continue
        bb = ir.cfg.blocks[idx]
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa PhiNode
                region_edge_count = count(e -> e in region_blocks, stmt.edges)
                region_edge_count >= 2 && return idx
            end
        end
    end

    return nothing
end

"""
    collect_proper_merge_phis(merge_idx, region_blocks, ir)

Collect phi nodes from a merge block that have edges from within the region.
Returns a vector of (ssa_idx, edge_values) named tuples.
"""
function collect_proper_merge_phis(merge_idx::Int, region_blocks::Set{Int}, ir::IRCode)
    merge_phis = @NamedTuple{ssa_idx::Int, edge_values::Dict{Int,Any}}[]
    merge_bb = ir.cfg.blocks[merge_idx]
    for si in first(merge_bb.stmts):last(merge_bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa PhiNode || continue
        edge_values = Dict{Int,Any}()
        for (edge_idx, edge) in enumerate(stmt.edges)
            if isassigned(stmt.values, edge_idx) && edge in region_blocks
                edge_values[edge] = stmt.values[edge_idx]
            end
        end
        isempty(edge_values) || push!(merge_phis, (ssa_idx=si, edge_values=edge_values))
    end
    return merge_phis
end

"""
    build_proper_branch!(branch_blk, target, from_block, merge_idx, merge_phis,
                          region_blocks, ir, ctx, subtree_map)

Build a branch block for a proper region by following the path from `target` to the
merge block, creating nested IfOps at branch points.

`from_block` is the block that branches to `target` (needed for merge phi lookup
when the target goes directly to the merge).

`subtree_map` maps block indices to their control tree sub-trees; when the path
encounters such a block, the sub-tree is processed via `tree_to_block` instead of
walking raw IR blocks (needed for nested patterns like `||` with `&&`).
"""
function build_proper_branch!(branch_blk::Block, target::Union{Int,Nothing},
                               from_block::Int, merge_idx::Int,
                               merge_phis,
                               region_blocks::Set{Int},
                               ir::IRCode, ctx::StructurizationContext,
                               subtree_map::Dict{Int, ControlTree}=Dict{Int, ControlTree}())
    nblocks = length(ir.cfg.blocks)

    # If target is the merge or outside region, yield merge phi values
    if target === nothing || target == merge_idx ||
       !(target in region_blocks) || !(1 <= target <= nblocks)
        branch_blk.terminator = yield_for_merge_edge(from_block, merge_phis, ctx)
        return
    end

    # Walk the path from target, emitting statements
    current = target
    while true
        # Check if current block is the root of a control tree sub-tree.
        # If so, process via tree_to_block (handles internal phis, IfOps, etc.)
        subtree = get(subtree_map, current, nothing)
        if subtree !== nothing
            sub_block = tree_to_block(subtree, ir, ctx)
            # Merge sub-tree results into branch_blk
            for (idx, entry) in sub_block.body
                push!(branch_blk, idx, entry.stmt, entry.typ)
            end
            # Find the exit successor of the sub-tree (next block on the path)
            sub_blocks = get_region_blocks(subtree, ir)
            next = nothing
            for b in sub_blocks
                1 <= b <= nblocks || continue
                for succ in ir.cfg.blocks[b].succs
                    if !(succ in sub_blocks) && (succ in region_blocks || succ == merge_idx)
                        next = succ
                        break
                    end
                end
                next !== nothing && break
            end
            if next === nothing || next == merge_idx
                # Sub-tree exits to merge
                exit_idx = get_exit_block(subtree, ir, sub_blocks)
                branch_blk.terminator = yield_for_merge_edge(exit_idx, merge_phis, ctx)
                return
            end
            current = next
            continue
        end

        bb = ir.cfg.blocks[current]

        # Emit non-control-flow statements (skip phis — they may have been
        # resolved by a preceding sub-tree's getfield at the same SSA index)
        gotoifnot = nothing
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa GotoIfNot
                gotoifnot = stmt
            elseif !(stmt isa GotoNode || stmt isa ReturnNode || stmt isa PhiNode)
                push!(branch_blk, si, stmt, ir.stmts.type[si])
            end
        end

        if gotoifnot !== nothing
            # Nested branch — create inner IfOp
            cond_value = find_condition_value(current, ir)
            false_target = gotoifnot.dest
            true_target = nothing
            for succ in ir.cfg.blocks[current].succs
                succ != false_target && (true_target = succ; break)
            end

            then_inner = Block()
            else_inner = Block()
            build_proper_branch!(then_inner, true_target, current, merge_idx,
                                  merge_phis, region_blocks, ir, ctx, subtree_map)
            build_proper_branch!(else_inner, false_target, current, merge_idx,
                                  merge_phis, region_blocks, ir, ctx, subtree_map)

            inner_if = IfOp(cond_value, then_inner, else_inner)

            # Use synthesized SSA indices for getfield (these are intermediate
            # results inside a branch, not the final merge phi indices)
            phi_types = Any[ctx.ssavaluetypes[phi.ssa_idx] for phi in merge_phis]
            gf_indices = Int[]
            for _ in merge_phis
                push!(gf_indices, ctx.next_value_idx)
                ctx.next_value_idx += 1
            end
            emit_ifop_result!(branch_blk, inner_if, gf_indices, phi_types, ctx)
            branch_blk.terminator = if !isempty(gf_indices)
                YieldOp(IRValue[SSAValue(idx) for idx in gf_indices])
            else
                YieldOp()
            end
            return
        end

        # No branch — follow to next block
        next = nothing
        for succ in ir.cfg.blocks[current].succs
            next = succ
            break
        end

        if next === nothing || next == merge_idx
            # Reached merge
            branch_blk.terminator = yield_for_merge_edge(current, merge_phis, ctx)
            return
        end

        if !(next in region_blocks) || !(1 <= next <= nblocks)
            # Exited region (shouldn't normally happen)
            branch_blk.terminator = yield_for_merge_edge(current, merge_phis, ctx)
            return
        end

        current = next
    end
end

"""
    yield_for_merge_edge(pred_block, merge_phis, ctx) -> YieldOp

Create a YieldOp with values from the merge phis for the given predecessor edge.
"""
function yield_for_merge_edge(pred_block::Int, merge_phis, ctx::StructurizationContext)
    yield_values = IRValue[]
    for phi in merge_phis
        val = get(phi.edge_values, pred_block, nothing)
        push!(yield_values, val !== nothing ? val : Undef(ctx.ssavaluetypes[phi.ssa_idx]))
    end
    return YieldOp(yield_values)
end
