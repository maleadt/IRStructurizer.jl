# control tree to structured IR conversion
#
# Two-phase approach:
# Phase 1: Convert ControlTree to structured IR with LoopOp for all loops (no SSA substitutions)
# Phase 2: Walk outer→inner, upgrade LoopOp to ForOp/WhileOp and apply local substitutions

export StructuredCodeInfo, structurize!

using Graphs: SimpleDiGraph, add_edge!, vertices, edges, nv, ne,
              inneighbors, outneighbors, Edge

#=============================================================================
 Phase 1: Control Tree to Structured IR (no substitutions)
=============================================================================#

"""
    control_tree_to_structured_ir(ctree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}) -> Block

Convert a control tree to structured IR entry block.
All loops become LoopOp (no pattern matching yet, no substitutions).
"""
function control_tree_to_structured_ir(ctree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo})
    block_id = Ref(1)
    entry_block = tree_to_block(ctree, code, blocks, block_id)
    return entry_block
end

"""
    tree_to_block(tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int}) -> Block

Convert a control tree node to a Block. Creates Statement objects with raw expressions (no substitutions).
"""
function tree_to_block(tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    idx = node_index(tree)
    rtype = region_type(tree)
    id = block_id[]
    block_id[] += 1

    block = Block(id)

    if rtype == REGION_BLOCK
        handle_block_region!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_IF_THEN_ELSE
        handle_if_then_else!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_IF_THEN
        handle_if_then!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_TERMINATION
        handle_termination!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_WHILE_LOOP || rtype == REGION_NATURAL_LOOP
        handle_loop!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_SELF_LOOP
        handle_self_loop!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_PROPER
        handle_proper_region!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_SWITCH
        handle_switch!(block, tree, code, blocks, block_id)
    else
        # Fallback: collect statements
        handle_block_region!(block, tree, code, blocks, block_id)
    end

    # Set terminator if not already set
    set_block_terminator!(block, code, blocks)

    return block
end

"""
    handle_block_region!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle REGION_BLOCK - a linear sequence of blocks.
"""
function handle_block_region!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    if isempty(children(tree))
        # Leaf node - collect statements from the block
        idx = node_index(tree)
        if 1 <= idx <= length(blocks)
            collect_block_statements!(block, blocks[idx], code)
        end
    else
        # Non-leaf - process children in order
        for child in children(tree)
            child_rtype = region_type(child)
            if child_rtype == REGION_BLOCK
                handle_block_region!(block, child, code, blocks, block_id)
            else
                # Nested control flow - create appropriate op
                handle_nested_region!(block, child, code, blocks, block_id)
            end
        end
    end
end

"""
    handle_nested_region!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle a nested control flow region.
"""
function handle_nested_region!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    rtype = region_type(tree)

    if rtype == REGION_IF_THEN_ELSE
        handle_if_then_else!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_IF_THEN
        handle_if_then!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_TERMINATION
        handle_termination!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_WHILE_LOOP || rtype == REGION_NATURAL_LOOP
        handle_loop!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_SELF_LOOP
        handle_self_loop!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_PROPER
        handle_proper_region!(block, tree, code, blocks, block_id)
    elseif rtype == REGION_SWITCH
        handle_switch!(block, tree, code, blocks, block_id)
    else
        handle_block_region!(block, tree, code, blocks, block_id)
    end
end

"""
    handle_if_then_else!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle REGION_IF_THEN_ELSE.
"""
function handle_if_then_else!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    tree_children = children(tree)
    length(tree_children) >= 3 || return handle_block_region!(block, tree, code, blocks, block_id)

    # First child is the condition block
    cond_tree = tree_children[1]
    cond_idx = node_index(cond_tree)

    # Collect condition block statements and find condition
    if 1 <= cond_idx <= length(blocks)
        cond_block = blocks[cond_idx]
        for si in cond_block.range
            stmt = code.code[si]
            if !(stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode || stmt isa PhiNode)
                push!(block.body, Statement(si, stmt, code.ssavaluetypes[si]))
            end
        end
    end

    cond_value = find_condition_value(cond_idx, code, blocks)

    # Then and else blocks
    then_tree = tree_children[2]
    else_tree = tree_children[3]

    then_block = tree_to_block(then_tree, code, blocks, block_id)
    else_block = tree_to_block(else_tree, code, blocks, block_id)

    # Create IfOp
    if_op = IfOp(cond_value, then_block, else_block, SSAValue[])
    push!(block.body, if_op)
end

"""
    handle_if_then!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle REGION_IF_THEN.
"""
function handle_if_then!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    tree_children = children(tree)
    length(tree_children) >= 2 || return handle_block_region!(block, tree, code, blocks, block_id)

    # First child is the condition block
    cond_tree = tree_children[1]
    cond_idx = node_index(cond_tree)

    # Collect condition block statements
    if 1 <= cond_idx <= length(blocks)
        cond_block = blocks[cond_idx]
        for si in cond_block.range
            stmt = code.code[si]
            if !(stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode || stmt isa PhiNode)
                push!(block.body, Statement(si, stmt, code.ssavaluetypes[si]))
            end
        end
    end

    cond_value = find_condition_value(cond_idx, code, blocks)

    # Then block
    then_tree = tree_children[2]
    then_block = tree_to_block(then_tree, code, blocks, block_id)

    # Empty else block
    else_block = Block(block_id[])
    block_id[] += 1

    if_op = IfOp(cond_value, then_block, else_block, SSAValue[])
    push!(block.body, if_op)
end

"""
    handle_termination!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle REGION_TERMINATION - branches where some paths terminate.
"""
function handle_termination!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    tree_children = children(tree)
    isempty(tree_children) && return handle_block_region!(block, tree, code, blocks, block_id)

    # First child is the condition block
    cond_tree = tree_children[1]
    cond_idx = node_index(cond_tree)

    # Collect condition block statements
    if 1 <= cond_idx <= length(blocks)
        cond_block = blocks[cond_idx]
        for si in cond_block.range
            stmt = code.code[si]
            if !(stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode || stmt isa PhiNode)
                push!(block.body, Statement(si, stmt, code.ssavaluetypes[si]))
            end
        end
    end

    cond_value = find_condition_value(cond_idx, code, blocks)

    # Build then and else blocks from remaining children
    if length(tree_children) >= 3
        then_tree = tree_children[2]
        else_tree = tree_children[3]
        then_block = tree_to_block(then_tree, code, blocks, block_id)
        else_block = tree_to_block(else_tree, code, blocks, block_id)
        if_op = IfOp(cond_value, then_block, else_block, SSAValue[])
        push!(block.body, if_op)
    elseif length(tree_children) == 2
        then_tree = tree_children[2]
        then_block = tree_to_block(then_tree, code, blocks, block_id)
        else_block = Block(block_id[])
        block_id[] += 1
        if_op = IfOp(cond_value, then_block, else_block, SSAValue[])
        push!(block.body, if_op)
    end
end

"""
    handle_loop!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle REGION_WHILE_LOOP and REGION_NATURAL_LOOP.
Phase 1: Always creates LoopOp with metadata. Pattern matching happens in Phase 2.
"""
function handle_loop!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    loop_op = build_loop_op_phase1(tree, code, blocks, block_id)
    push!(block.body, loop_op)
end

"""
    handle_self_loop!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle REGION_SELF_LOOP.
"""
function handle_self_loop!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    idx = node_index(tree)

    body_block = Block(block_id[])
    block_id[] += 1

    if 1 <= idx <= length(blocks)
        collect_block_statements!(body_block, blocks[idx], code)
    end

    loop_op = LoopOp(IRValue[], body_block, SSAValue[], idx, Set{Int}([idx]))
    push!(block.body, loop_op)
end

"""
    handle_proper_region!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle REGION_PROPER - acyclic region not matching other patterns.
"""
function handle_proper_region!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    # Process as a sequence of blocks
    handle_block_region!(block, tree, code, blocks, block_id)
end

"""
    handle_switch!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})

Handle REGION_SWITCH.
"""
function handle_switch!(block::Block, tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    # For now, handle as a nested if-else chain
    # TODO: Implement proper switch handling if needed
    handle_block_region!(block, tree, code, blocks, block_id)
end

"""
    collect_block_statements!(block::Block, info::BlockInfo, code::CodeInfo)

Collect statements from a BlockInfo into a Block, excluding control flow.
Creates Statement objects with raw expressions (no substitutions).
"""
function collect_block_statements!(block::Block, info::BlockInfo, code::CodeInfo)
    stmts = code.code
    types = code.ssavaluetypes
    for si in info.range
        stmt = stmts[si]
        if stmt isa ReturnNode
            block.terminator = stmt
        elseif !(stmt isa GotoNode || stmt isa GotoIfNot || stmt isa PhiNode)
            push!(block.body, Statement(si, stmt, types[si]))
        end
    end
end

"""
    find_condition_value(block_idx::Int, code::CodeInfo, blocks::Vector{BlockInfo}) -> IRValue

Find the condition value for a GotoIfNot in the given block.
"""
function find_condition_value(block_idx::Int, code::CodeInfo, blocks::Vector{BlockInfo})
    block_idx < 1 || block_idx > length(blocks) && return SSAValue(1)

    block = blocks[block_idx]
    for si in block.range
        stmt = code.code[si]
        if stmt isa GotoIfNot
            cond = stmt.cond
            if cond isa SSAValue || cond isa SlotNumber || cond isa Argument
                return cond
            else
                return SSAValue(max(1, si - 1))
            end
        end
    end

    return SSAValue(max(1, first(block.range)))
end

"""
    set_block_terminator!(block::Block, code::CodeInfo, blocks::Vector{BlockInfo})

Set the block terminator based on statements.
"""
function set_block_terminator!(block::Block, code::CodeInfo, blocks::Vector{BlockInfo})
    block.terminator !== nothing && return

    # Find the last statement index in body
    last_idx = nothing
    for item in reverse(block.body)
        if item isa Statement
            last_idx = item.idx
            break
        end
    end
    if last_idx !== nothing && last_idx < length(code.code)
        next_stmt = code.code[last_idx + 1]
        if next_stmt isa ReturnNode
            block.terminator = next_stmt
        end
    end
end

"""
    build_loop_op_phase1(tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int}) -> LoopOp

Build a LoopOp with metadata for Phase 1. No substitutions applied yet.
Pattern detection and substitution happens in Phase 2.
"""
function build_loop_op_phase1(tree::ControlTree, code::CodeInfo, blocks::Vector{BlockInfo}, block_id::Ref{Int})
    stmts = code.code
    types = code.ssavaluetypes
    header_idx = node_index(tree)
    loop_blocks = get_loop_blocks(tree, blocks)

    @assert 1 <= header_idx <= length(blocks) "Invalid header_idx from control tree: $header_idx"
    header_block = blocks[header_idx]
    stmt_to_blk = stmt_to_block_map(blocks, length(stmts))

    # Find phi nodes in header - these become loop-carried values and results
    init_values = IRValue[]
    carried_values = IRValue[]
    block_args = BlockArg[]
    result_vars = SSAValue[]

    for si in header_block.range
        stmt = stmts[si]
        if stmt isa PhiNode
            push!(result_vars, SSAValue(si))
            phi = stmt

            entry_val = nothing
            carried_val = nothing

            for (edge_idx, _) in enumerate(phi.edges)
                if isassigned(phi.values, edge_idx)
                    val = phi.values[edge_idx]

                    if val isa SSAValue
                        val_stmt = val.id
                        if val_stmt > 0 && val_stmt <= length(stmts)
                            val_block = stmt_to_blk[val_stmt]
                            if val_block ∈ loop_blocks
                                carried_val = val
                            else
                                entry_val = convert_phi_value(val)
                            end
                        else
                            entry_val = convert_phi_value(val)
                        end
                    else
                        entry_val = convert_phi_value(val)
                    end
                end
            end

            entry_val !== nothing && push!(init_values, entry_val)
            carried_val !== nothing && push!(carried_values, carried_val)

            phi_type = types[si]
            push!(block_args, BlockArg(length(block_args) + 1, phi_type))
        end
    end

    # Build loop body block
    body = Block(block_id[])
    block_id[] += 1
    body.args = block_args

    # Find the condition for loop exit
    condition = nothing
    for si in header_block.range
        stmt = stmts[si]
        if stmt isa GotoIfNot
            condition = stmt.cond
            break
        end
    end

    # Collect header statements (excluding phi nodes and control flow) - NO SUBSTITUTION
    for si in header_block.range
        stmt = stmts[si]
        if !(stmt isa PhiNode || stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode)
            push!(body.body, Statement(si, stmt, types[si]))
        end
    end

    # Create the conditional structure inside the loop body
    if condition !== nothing
        cond_value = convert_phi_value(condition)

        then_block = Block(block_id[])
        block_id[] += 1

        # Process loop body blocks (excluding header)
        for child in children(tree)
            child_idx = node_index(child)
            if child_idx != header_idx
                handle_block_region!(then_block, child, code, blocks, block_id)
            end
        end
        # Raw carried values (no substitution yet)
        then_block.terminator = ContinueOp(carried_values)

        else_block = Block(block_id[])
        block_id[] += 1
        # Block args are the references for break
        result_values = IRValue[]
        for arg in block_args
            push!(result_values, arg)
        end
        else_block.terminator = BreakOp(result_values)

        if_op = IfOp(cond_value, then_block, else_block, SSAValue[])
        push!(body.body, if_op)
    else
        # No condition - process children directly
        for child in children(tree)
            child_idx = node_index(child)
            if child_idx != header_idx
                handle_block_region!(body, child, code, blocks, block_id)
            end
        end
        body.terminator = ContinueOp(carried_values)
    end

    return LoopOp(init_values, body, result_vars, header_idx, loop_blocks)
end

#=============================================================================
 Phase 2a: Apply SSA Substitutions (outer → inner)
=============================================================================#

"""
    apply_loop_substitutions!(block::Block)

Apply SSA→BlockArg substitutions to all loops, processing outer→inner.
Must be called before pattern matching.
"""
function apply_loop_substitutions!(block::Block)
    for item in block.body
        if item isa LoopOp
            subs = compute_loop_subs(item)
            substitute_block!(item.body, subs)
            apply_loop_substitutions!(item.body)
        elseif item isa IfOp
            apply_loop_substitutions!(item.then_block)
            apply_loop_substitutions!(item.else_block)
        end
    end
end

#=============================================================================
 Phase 2b: Pattern Matching (upgrade LoopOp → ForOp/WhileOp)
=============================================================================#

"""
    apply_loop_patterns!(block::Block, code::CodeInfo, blocks::Vector{BlockInfo})

Upgrade LoopOps to ForOp/WhileOp where patterns match.
Assumes substitutions have already been applied.
"""
function apply_loop_patterns!(block::Block, code::CodeInfo, blocks::Vector{BlockInfo})
    for (i, item) in enumerate(block.body)
        if item isa LoopOp
            upgraded = try_upgrade_loop(item, code, blocks)
            if upgraded !== nothing
                block.body[i] = upgraded
                apply_loop_patterns!(upgraded.body, code, blocks)
            else
                apply_loop_patterns!(item.body, code, blocks)
            end
        elseif item isa IfOp
            apply_loop_patterns!(item.then_block, code, blocks)
            apply_loop_patterns!(item.else_block, code, blocks)
        end
    end
end

"""
    compute_loop_subs(loop::LoopOp) -> Substitutions

Compute the SSA→BlockArg substitutions for a loop.
Maps each phi node SSA index to its corresponding block argument.
"""
function compute_loop_subs(loop::LoopOp)
    @assert length(loop.result_vars) == length(loop.body.args) "Mismatch between result_vars and body.args"
    subs = Substitutions()
    for (i, result_var) in enumerate(loop.result_vars)
        subs[result_var.id] = loop.body.args[i]
    end
    return subs
end

"""
    try_upgrade_loop(loop::LoopOp, code::CodeInfo, blocks::Vector{BlockInfo}) -> Union{ForOp, WhileOp, Nothing}

Try to upgrade a LoopOp to a more specific loop type (ForOp or WhileOp).
Returns the upgraded op, or nothing if no pattern matches.
"""
function try_upgrade_loop(loop::LoopOp, code::CodeInfo, blocks::Vector{BlockInfo})
    @assert loop.header_idx != 0 "LoopOp missing header_idx metadata"

    # Try ForOp pattern first
    for_op = try_upgrade_to_for(loop, code, blocks)
    for_op !== nothing && return for_op

    # Try WhileOp pattern
    while_op = try_upgrade_to_while(loop, code, blocks)
    while_op !== nothing && return while_op

    return nothing
end

"""
    try_upgrade_to_for(loop::LoopOp, code::CodeInfo, blocks::Vector{BlockInfo}) -> Union{ForOp, Nothing}

Try to upgrade a LoopOp to a ForOp by detecting the for-loop pattern.
"""
function try_upgrade_to_for(loop::LoopOp, code::CodeInfo, blocks::Vector{BlockInfo})
    stmts = code.code
    header_idx = loop.header_idx
    loop_blocks = loop.loop_blocks

    @assert 1 <= header_idx <= length(blocks) "Invalid header_idx: $header_idx"
    header = blocks[header_idx]

    # Find the GotoIfNot condition in header
    cond_var = nothing
    for si in header.range
        stmt = stmts[si]
        if stmt isa GotoIfNot
            cond_var = stmt.cond
            break
        end
    end
    cond_var === nothing && return nothing
    cond_var isa SSAValue || return nothing

    # Trace to comparison: slt_int(%iv, %upper)
    cond_var.id < 1 || cond_var.id > length(stmts) && return nothing
    cond_stmt = stmts[cond_var.id]
    cond_stmt isa Expr || return nothing
    cond_stmt.head === :call || return nothing

    func = cond_stmt.args[1]
    is_less_than = func isa GlobalRef && func.name in (:slt_int, :ult_int)
    is_less_than || return nothing

    iv_candidate = cond_stmt.args[2]  # induction variable
    upper_bound_raw = cond_stmt.args[3]   # upper bound

    # The iv_candidate should be a phi node in the header
    iv_candidate isa SSAValue || return nothing
    iv_phi_idx = iv_candidate.id
    iv_phi_idx < 1 || iv_phi_idx > length(stmts) && return nothing
    iv_phi_stmt = stmts[iv_phi_idx]
    iv_phi_stmt isa PhiNode || return nothing

    # Verify the phi is in the header
    iv_phi_idx in header.range || return nothing

    stmt_to_blk = stmt_to_block_map(blocks, length(stmts))

    # Extract lower bound (init value from outside loop)
    lower_bound = nothing
    for (edge_idx, _) in enumerate(iv_phi_stmt.edges)
        if isassigned(iv_phi_stmt.values, edge_idx)
            val = iv_phi_stmt.values[edge_idx]
            if !is_value_in_loop(val, stmts, stmt_to_blk, loop_blocks)
                lower_bound = convert_phi_value(val)
                break
            end
        end
    end
    lower_bound === nothing && return nothing

    # Find step and iv_incr_idx by looking for add_int(iv_phi, step) in loop body
    step_raw = nothing
    iv_incr_idx = 0
    for bi in loop_blocks
        bi < 1 || bi > length(blocks) && continue
        for si in blocks[bi].range
            stmt = stmts[si]
            if stmt isa Expr && stmt.head === :call
                func = stmt.args[1]
                if func isa GlobalRef && func.name === :add_int
                    if length(stmt.args) >= 2 && stmt.args[2] isa SSAValue && stmt.args[2].id == iv_phi_idx
                        step_raw = stmt.args[3]
                        iv_incr_idx = si
                        break
                    end
                end
            end
        end
        step_raw !== nothing && break
    end
    step_raw === nothing && return nothing

    # Verify step and upper bound are loop-invariant
    if is_value_in_loop(step_raw, stmts, stmt_to_blk, loop_blocks)
        return nothing
    end
    if is_value_in_loop(upper_bound_raw, stmts, stmt_to_blk, loop_blocks)
        return nothing
    end
    step = convert_phi_value(step_raw)
    upper_bound = convert_phi_value(upper_bound_raw)

    # Build ForOp from the existing LoopOp structure
    # The body already has substitutions applied, we just need to:
    # 1. Identify induction variable's block arg
    # 2. Remove the IfOp condition structure (bounds are implicit in ForOp)
    # 3. Filter out iv increment and condition comparison statements

    # Find which result_var/block_arg corresponds to the induction variable
    iv_result_idx = findfirst(rv -> rv.id == iv_phi_idx, loop.result_vars)
    iv_result_idx === nothing && return nothing
    iv_ssa = loop.result_vars[iv_result_idx]
    iv_arg = loop.body.args[iv_result_idx]

    # Separate non-IV carried values
    other_result_vars = SSAValue[]
    other_init_values = IRValue[]
    for (j, rv) in enumerate(loop.result_vars)
        if j != iv_result_idx && j <= length(loop.init_values)
            push!(other_result_vars, rv)
            push!(other_init_values, loop.init_values[j])
        end
    end

    # Rebuild body block without condition structure
    # LoopOp body: [header_stmts..., IfOp(cond, continue_block, break_block)]
    # ForOp body: [body_stmts...] with ContinueOp terminator
    new_body = Block(loop.body.id)
    new_body.args = copy(loop.body.args)  # Keep same block args (already substituted)

    # Extract body statements, filtering out iv-related ones
    for item in loop.body.body
        if item isa Statement
            # Skip iv increment and condition comparison
            item.idx == iv_incr_idx && continue
            orig_stmt = stmts[item.idx]
            if orig_stmt isa Expr && orig_stmt.head === :call
                func = orig_stmt.args[1]
                func isa GlobalRef && func.name in (:slt_int, :ult_int) && continue
            end
            push!(new_body.body, item)
        elseif item isa IfOp
            # Extract the continue path's body (skip condition check structure)
            for sub_item in item.then_block.body
                if sub_item isa Statement
                    sub_item.idx == iv_incr_idx && continue
                    push!(new_body.body, sub_item)
                else
                    push!(new_body.body, sub_item)
                end
            end
        else
            push!(new_body.body, item)
        end
    end

    # Get yield values from continue terminator, excluding the IV
    yield_values = IRValue[]
    if !isempty(loop.body.body)
        last_item = loop.body.body[end]
        if last_item isa IfOp && last_item.then_block.terminator isa ContinueOp
            for (j, v) in enumerate(last_item.then_block.terminator.values)
                j != iv_result_idx && push!(yield_values, v)
            end
        end
    end
    new_body.terminator = ContinueOp(yield_values)

    return ForOp(lower_bound, upper_bound, step, iv_ssa, iv_arg,
                 other_init_values, new_body, other_result_vars)
end

"""
    try_upgrade_to_while(loop::LoopOp, code::CodeInfo, blocks::Vector{BlockInfo}) -> Union{WhileOp, Nothing}

Try to upgrade a LoopOp to a WhileOp by detecting the while-loop pattern.
"""
function try_upgrade_to_while(loop::LoopOp, code::CodeInfo, blocks::Vector{BlockInfo})
    # Build WhileOp from the existing LoopOp structure
    # The body already has substitutions applied from Phase 2a

    # Find the IfOp in the loop body - its condition is the while condition (already substituted)
    condition_ifop = nothing
    for item in loop.body.body
        if item isa IfOp
            condition_ifop = item
            break
        end
    end
    condition_ifop === nothing && return nothing

    # Rebuild body without the IfOp condition structure
    new_body = Block(loop.body.id)
    new_body.args = copy(loop.body.args)

    # Extract statements and the continue path from the IfOp
    for item in loop.body.body
        if item isa Statement
            push!(new_body.body, item)
        elseif item isa IfOp
            # This is the condition check - extract the continue path's body
            for sub_item in item.then_block.body
                push!(new_body.body, sub_item)
            end
        else
            push!(new_body.body, item)
        end
    end

    # Get yield values from the continue terminator
    yield_values = IRValue[]
    if !isempty(loop.body.body)
        last_item = loop.body.body[end]
        if last_item isa IfOp && last_item.then_block.terminator isa ContinueOp
            yield_values = copy(last_item.then_block.terminator.values)
        end
    end
    new_body.terminator = ContinueOp(yield_values)

    return WhileOp(condition_ifop.condition, loop.init_values, new_body, loop.result_vars)
end

#=============================================================================
 Public API
=============================================================================#

"""
    structurize!(sci::StructuredCodeInfo; loop_patterning=true) -> StructuredCodeInfo

Convert unstructured control flow in `sci` to structured control flow operations
(IfOp, ForOp, WhileOp, LoopOp) in-place.

This transforms GotoNode and GotoIfNot statements into nested structured ops
that can be traversed hierarchically.

Two-phase approach:
1. Build structure with LoopOp for all loops (no SSA substitutions)
2. Walk outer→inner, upgrade loops and apply local substitutions

When `loop_patterning=true` (default), loops are classified as ForOp (bounded counters)
or WhileOp (condition-based). When `false`, all loops become LoopOp.

Returns `sci` for convenience (allows chaining).
"""
function structurize!(sci::StructuredCodeInfo; loop_patterning::Bool=true)
    code = sci.code
    stmts = code.code
    types = code.ssavaluetypes
    n = length(stmts)

    n == 0 && return sci

    # Check if the code is straight-line (no control flow)
    has_control_flow = any(s -> s isa GotoNode || s isa GotoIfNot, stmts)

    if !has_control_flow
        # Straight-line code - no substitutions needed
        new_entry = Block(1)
        for i in 1:n
            stmt = stmts[i]
            if stmt isa ReturnNode
                new_entry.terminator = stmt
            elseif !(stmt isa GotoNode || stmt isa GotoIfNot)
                push!(new_entry.body, Statement(i, stmt, types[i]))
            end
        end
        sci.entry = new_entry
        return sci
    end

    # Build block-level CFG
    blocks, cfg = build_block_cfg(code)

    # Build control tree using SPIRV.jl-style graph contraction
    ctree = ControlTree(cfg)

    # Phase 1: Convert control tree to structured IR (LoopOp for all loops, no subs)
    sci.entry = control_tree_to_structured_ir(ctree, code, blocks)

    # Phase 2a: Apply SSA substitutions (always)
    apply_loop_substitutions!(sci.entry)

    # Phase 2b: Upgrade loop patterns (optional)
    if loop_patterning
        apply_loop_patterns!(sci.entry, code, blocks)
    end

    return sci
end
