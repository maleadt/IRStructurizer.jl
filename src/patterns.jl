# Pattern matching and loop upgrades (WhileOp/LoopOp → ForOp)

using MLStyle: @active, @match, Some

#=============================================================================
 MLStyle Active Patterns for For-Loop Detection
=============================================================================#

# Match a for-loop condition: slt_int(iv, bound) or ult_int(iv, bound)
# Returns (iv, iv_idx, upper) if matched, nothing otherwise
@active for_condition_pattern(args) begin
    (expr, body_args) = args
    expr isa Expr || return nothing
    expr.head === :call || return nothing
    length(expr.args) >= 3 || return nothing

    func = expr.args[1]
    func isa GlobalRef || return nothing
    func.name in (:slt_int, :ult_int) || return nothing

    iv_candidate = expr.args[2]
    iv_candidate isa BlockArg || return nothing

    iv_idx = findfirst(==(iv_candidate), body_args)
    iv_idx === nothing && return nothing

    upper_bound = expr.args[3]
    (iv_candidate, iv_idx, upper_bound)
end

# Match a for-loop step: add_int(iv, step)
# Returns Some(step) if matched, nothing otherwise (1-ary pattern needs Some)
@active for_step_pattern(args) begin
    (expr, iv_arg) = args
    expr isa Expr || return nothing
    expr.head === :call || return nothing
    length(expr.args) >= 3 || return nothing

    func = expr.args[1]
    func isa GlobalRef || return nothing
    func.name === :add_int || return nothing

    expr.args[2] == iv_arg || return nothing
    Some(expr.args[3])
end

# Match equality condition for Julia's for-loop: ===(BlockArg, upper_bound)
# Returns (iv_arg, iv_idx, upper_bound) if matched, nothing otherwise
@active for_equality_condition_pattern(args) begin
    (expr, body_args) = args
    expr isa Expr || return nothing
    expr.head === :call || return nothing
    length(expr.args) >= 3 || return nothing

    func = expr.args[1]
    # Match both Base.:(===) and :(===)
    if func isa GlobalRef
        func.name === :(===) || return nothing
    elseif func === :(===)
        # Direct symbol
    else
        return nothing
    end

    iv_candidate = expr.args[2]
    iv_candidate isa BlockArg || return nothing

    iv_idx = findfirst(==(iv_candidate), body_args)
    iv_idx === nothing && return nothing

    upper_bound = expr.args[3]
    (iv_candidate, iv_idx, upper_bound)
end

#=============================================================================
 Getfield Helper Functions (for tuple+getfield loop result handling)
=============================================================================#

"""
    find_getfields_for(block::Block, loop_ssa::SSAValue) -> Vector{NamedTuple}

Find all getfield expressions in the block that reference the given loop SSA value.
Returns a vector of (ssa_idx, field_idx) named tuples.
"""
function find_getfields_for(block::Block, loop_ssa::SSAValue)
    getfields = NamedTuple{(:ssa_idx, :field_idx), Tuple{Int, Int}}[]
    for (idx, entry) in block.body
        expr = entry.stmt
        if expr isa Expr && expr.head === :call &&
           length(expr.args) >= 3 && expr.args[1] === Core.getfield &&
           expr.args[2] == loop_ssa
            push!(getfields, (ssa_idx=idx, field_idx=expr.args[3]))
        end
    end
    return getfields
end

"""
    remove_stmt!(block::Block, ssa_idx::Int)

Remove a statement from the block by its SSA index.
"""
function remove_stmt!(block::Block, ssa_idx::Int)
    new_body = SSAVector()
    for (idx, entry) in block.body
        idx == ssa_idx || push!(new_body, (idx, entry.stmt, entry.typ))
    end
    block.body = new_body
end

#=============================================================================
 Helper Functions (Pattern matching on structured IR)
=============================================================================#

"""
    find_expr_by_ssa(block::Block, ssa::SSAValue) -> Union{Tuple{Int, SSAEntry}, Nothing}

Find an expression in the block whose SSA index matches the SSAValue's id.
Returns (idx, entry) tuple or nothing.
"""
function find_expr_by_ssa(block::Block, ssa::SSAValue)
    for (idx, entry) in block.body
        if !(entry.stmt isa ControlFlowOp) && idx == ssa.id
            return (idx, entry)
        end
    end
    return nothing
end

"""
    is_loop_invariant(val, block::Block, n_init_values::Int) -> Bool

Check if a value is loop-invariant (not defined inside the loop body).
- BlockArgs (all of which are init_values) are loop-variant (carries)
- SSAValues are loop-invariant (outer scope references)
- Constants and Arguments are always loop-invariant
"""
function is_loop_invariant(val, block::Block, n_init_values::Int)
    if val isa BlockArg
        return false
    end

    if val isa SSAValue
        return !defines(block, val)
    end

    # Constants, Arguments, etc. are invariant
    return true
end

"""
    defines(block::Block, ssa::SSAValue) -> Bool

Check if a block defines an SSA value (i.e., contains an expression that produces it).
Searches nested blocks recursively.
"""
function defines(block::Block, ssa::SSAValue)
    for (idx, entry) in block.body
        if entry.stmt isa ControlFlowOp
            defines_in_op(entry.stmt, ssa) && return true
        elseif idx == ssa.id
            return true
        end
    end
    return false
end

# Helper to check if an SSA is defined in a control flow op's regions
defines_in_op(op::IfOp, ssa::SSAValue) = defines(op.then_region, ssa) || defines(op.else_region, ssa)
defines_in_op(op::LoopOp, ssa::SSAValue) = defines(op.body, ssa)
defines_in_op(op::ForOp, ssa::SSAValue) = defines(op.body, ssa)
defines_in_op(op::WhileOp, ssa::SSAValue) = defines(op.before, ssa) || defines(op.after, ssa)

#=============================================================================
 Loop Pattern Matching (WhileOp → ForOp)
=============================================================================#

"""
    apply_loop_patterns!(block::Block, ctx::StructurizationContext)

Upgrade WhileOp/LoopOp to ForOp where patterns match.

For ForOp upgrades:
- The loop's key remains unchanged (no re-keying)
- The IV's getfield statement is removed from the parent block
- Remaining getfield indices are adjusted to account for the removed IV
- For LoopOp upgrades (Julia's `for i in 1:n`), the upper bound is adjusted +1
"""
function apply_loop_patterns!(block::Block, ctx::StructurizationContext)
    # Collect upgrades: (loop_key => (new_op, iv_getfield_idx, iv_field_idx))
    # iv_getfield_idx: SSA index of the IV's getfield (to remove), or nothing if no cleanup needed
    # iv_field_idx: field index of the IV in the tuple (to adjust other getfields)
    upgrades = Dict{Int, Tuple{ControlFlowOp, Union{Nothing, Int}, Int}}()

    # Separate dict for LoopOp upgrades that need upper bound adjustment
    # (loop_key => (ForOp, iv_getfield_idx, iv_field_idx, original_upper))
    loopop_upgrades = Dict{Int, Tuple{ForOp, Union{Nothing, Int}, Int, IRValue}}()

    for (idx, entry) in block.body
        if entry.stmt isa WhileOp
            # Use MLStyle pattern matching for WhileOp → ForOp
            result = try_upgrade_while_to_for(entry.stmt, ctx, idx, block)
            if result !== nothing
                upgrades[idx] = result
            end
        elseif entry.stmt isa LoopOp
            # Use MLStyle pattern matching for LoopOp → ForOp (Julia's for i in 1:n)
            result = try_upgrade_loopop_to_for(entry.stmt, ctx, idx, block)
            if result !== nothing
                loopop_upgrades[idx] = result
            end
        end
    end

    # Handle LoopOp upgrades: insert add_int for upper bound adjustment
    # We need to do this before the main upgrade pass to get the new SSA indices
    # Collect: loop_key => (adj_ssa_idx, add_int_expr)
    upper_bound_adjustments = Dict{Int, Tuple{Int, Expr}}()
    for (loop_key, (for_op, iv_getfield_idx, iv_field_idx, original_upper)) in loopop_upgrades
        # Allocate a synthesized SSA for the adjusted upper bound
        adj_ssa_idx = ctx.next_ssa_idx
        ctx.next_ssa_idx += 1
        adj_ssa = SSAValue(adj_ssa_idx)

        # Create add_int(original_upper, 1) expression
        add_int_expr = Expr(:call, GlobalRef(Base, :add_int), original_upper, 1)

        # Update the ForOp's upper bound to the new SSA
        for_op.upper = adj_ssa

        # Store for later insertion
        upper_bound_adjustments[loop_key] = (adj_ssa_idx, add_int_expr)

        # Store as regular upgrade for the main pass
        upgrades[loop_key] = (for_op, iv_getfield_idx, iv_field_idx)
    end

    # Apply upgrades: replace WhileOp/LoopOp with ForOp (same key!)
    if !isempty(upgrades)
        new_body = SSAVector()

        for (old_key, entry) in block.body
            # Insert any synthesized add_int statements before the loop they belong to
            if haskey(upper_bound_adjustments, old_key)
                adj_ssa_idx, add_int_expr = upper_bound_adjustments[old_key]
                push!(new_body, (adj_ssa_idx, add_int_expr, Int64))
            end

            if haskey(upgrades, old_key)
                new_op, _, _ = upgrades[old_key]
                # Update result type: ForOp has one fewer result
                new_typ = compute_upgraded_type(entry.typ, upgrades[old_key])
                push!(new_body, (old_key, new_op, new_typ))
            else
                push!(new_body, (old_key, entry.stmt, entry.typ))
            end
        end
        block.body = new_body

        # Remove IV getfields and adjust remaining getfield indices
        for (loop_key, (new_op, iv_getfield_idx, iv_field_idx)) in upgrades
            if new_op isa ForOp && iv_getfield_idx !== nothing
                remove_stmt!(block, iv_getfield_idx)
                # Adjust remaining getfield indices for this loop
                adjust_getfield_indices!(block, loop_key, iv_field_idx)
            end
        end
    end

    # Recurse into all control flow ops (including newly created ones)
    for stmt in statements(block.body)
        if stmt isa LoopOp
            apply_loop_patterns!(stmt.body, ctx)
        elseif stmt isa IfOp
            apply_loop_patterns!(stmt.then_region, ctx)
            apply_loop_patterns!(stmt.else_region, ctx)
        elseif stmt isa WhileOp
            apply_loop_patterns!(stmt.before, ctx)
            apply_loop_patterns!(stmt.after, ctx)
        elseif stmt isa ForOp
            apply_loop_patterns!(stmt.body, ctx)
        end
    end
end

"""
    compute_upgraded_type(old_typ, upgrade_info) -> Type

Compute the new result type after ForOp upgrade (one fewer result due to IV removal).
Always returns a Tuple type (uniform handling in codegen).
"""
function compute_upgraded_type(@nospecialize(old_typ), upgrade_info)
    new_op, _, iv_field_idx = upgrade_info

    # WhileOp keeps all results
    !(new_op isa ForOp) && return old_typ

    # Must be a Tuple type (uniform loop result handling)
    @assert old_typ <: Tuple "Expected Tuple type for loop results, got $old_typ"

    # Remove the IV's type from the tuple
    params = collect(old_typ.parameters)
    deleteat!(params, iv_field_idx)

    # Always return Tuple (may be empty Tuple{})
    return Tuple{params...}
end

"""
    adjust_getfield_indices!(block::Block, loop_key::Int, removed_field_idx::Int)

Adjust getfield field indices after removing the IV's getfield.
All getfields referencing the loop with field index > removed_field_idx
have their field index decremented.
"""
function adjust_getfield_indices!(block::Block, loop_key::Int, removed_field_idx::Int)
    loop_ssa = SSAValue(loop_key)
    for (idx, entry) in block.body
        expr = entry.stmt
        if expr isa Expr && expr.head === :call &&
           length(expr.args) >= 3 && expr.args[1] === Core.getfield &&
           expr.args[2] == loop_ssa
            old_field = expr.args[3]
            if old_field > removed_field_idx
                expr.args[3] = old_field - 1
            end
        end
    end
end

"""
    try_upgrade_while_to_for(while_op::WhileOp, ctx::StructurizationContext, current_key::Int, parent_block::Block)
        -> Union{Tuple{ForOp, Union{Nothing, Int}, Int}, Nothing}

Try to upgrade a WhileOp to ForOp using MLStyle pattern matching.
Returns (ForOp, iv_getfield_idx, iv_field_idx) if upgraded, or nothing if not upgraded.
"""
function try_upgrade_while_to_for(while_op::WhileOp, ctx::StructurizationContext, current_key::Int, parent_block::Block)
    before = while_op.before::Block
    after = while_op.after::Block
    n_init_values = length(while_op.init_values)

    # Get the condition from ConditionOp terminator
    cond_op = before.terminator
    cond_op isa ConditionOp || return nothing
    cond_val = cond_op.condition
    cond_val isa SSAValue || return nothing

    # Find the condition expression
    cond_entry = find_by_ssa(before.body, cond_val.id)
    cond_entry === nothing && return nothing
    cond_expr = cond_entry.stmt

    # Use MLStyle pattern matching for for-loop condition
    matched = @match (cond_expr, before.args) begin
        for_condition_pattern(iv, iv_idx, upper) => (iv, iv_idx, upper)
        _ => nothing
    end
    matched === nothing && return nothing
    iv_arg, iv_idx, upper_bound_raw = matched

    # Verify IV is in init_values range
    iv_idx > n_init_values && return nothing
    lower_bound = while_op.init_values[iv_idx]

    # Helper to resolve BlockArg to original value from init_values
    function resolve_blockarg(arg)
        if arg isa BlockArg && arg.id <= n_init_values
            return while_op.init_values[arg.id]
        end
        return arg
    end

    upper_bound = resolve_blockarg(upper_bound_raw)

    # Find the step in the after region using MLStyle pattern
    step_result = find_step_in_after(after, iv_arg)
    step_result === nothing && return nothing
    step_idx, step_raw = step_result
    step = resolve_blockarg(step_raw)

    # Verify upper_bound and step are loop-invariant
    is_loop_invariant(upper_bound, before, n_init_values) || return nothing
    is_loop_invariant(step, after, n_init_values) || return nothing

    # Separate non-IV init_values
    other_init_values = IRValue[]
    for (j, v) in enumerate(while_op.init_values)
        j != iv_idx && push!(other_init_values, v)
    end

    # Find the IV's getfield in the parent block
    loop_ssa = SSAValue(current_key)
    getfields = find_getfields_for(parent_block, loop_ssa)
    iv_getfield_idx = nothing
    for gf in getfields
        if gf.field_idx == iv_idx
            iv_getfield_idx = gf.ssa_idx
            break
        end
    end

    # Build ForOp body from after region, filtering out IV-related items
    new_body = Block()
    new_body.args = [arg for arg in after.args if arg != iv_arg]

    for (idx, entry) in after.body
        idx == step_idx && continue
        push!(new_body, idx, entry.stmt, entry.typ)
    end

    # Get yield values from YieldOp, excluding the IV
    yield_values = IRValue[]
    if after.terminator isa YieldOp
        for (j, v) in enumerate(after.terminator.values)
            j != iv_idx && j <= n_init_values && push!(yield_values, v)
        end
    end
    new_body.terminator = ContinueOp(yield_values)

    # Create ForOp
    for_op = ForOp(lower_bound, upper_bound, step, iv_arg, new_body, other_init_values)
    return (for_op, iv_getfield_idx, iv_idx)
end

"""
    find_step_in_after(block::Block, iv_arg::BlockArg) -> Union{Tuple{Int, Any}, Nothing}

Find the step expression `add_int(iv_arg, step)` in the after region.
Returns (ssa_idx, step_value) or nothing.
"""
function find_step_in_after(block::Block, iv_arg::BlockArg)
    for (idx, entry) in block.body
        if !(entry.stmt isa ControlFlowOp)
            matched = @match (entry.stmt, iv_arg) begin
                for_step_pattern(step) => step
                _ => nothing
            end
            if matched !== nothing
                return (idx, matched)
            end
        end
    end
    return nothing
end

#=============================================================================
 LoopOp → ForOp Pattern Matching (for Julia's `for i in 1:n`)
=============================================================================#

"""
    try_upgrade_loopop_to_for(loop_op::LoopOp, ctx::StructurizationContext, current_key::Int, parent_block::Block)
        -> Union{Tuple{ForOp, Union{Nothing, Int}, Int, IRValue}, Nothing}

Try to upgrade a LoopOp to ForOp for Julia's `for i in 1:n` pattern.
Returns (ForOp, iv_getfield_idx, iv_field_idx, upper_bound_adj) if upgraded, or nothing.

The upper_bound_adj is the adjusted upper bound expression that needs to be inserted
in the parent block before the ForOp.

Julia's `for i in 1:n` pattern in LoopOp:
- Body contains an IfOp with `=== (BlockArg, upper_bound)` condition
- One branch has ContinueOp with step (add_int on IV)
- Other branch has BreakOp
- Bound needs +1 adjustment (inclusive to exclusive)
"""
function try_upgrade_loopop_to_for(loop_op::LoopOp, ctx::StructurizationContext, current_key::Int, parent_block::Block)
    body = loop_op.body::Block
    n_init_values = length(loop_op.init_values)

    # Find the terminating IfOp in the body
    if_op = nothing
    if_idx = nothing
    for (idx, entry) in body.body
        if entry.stmt isa IfOp
            if_op = entry.stmt
            if_idx = idx
        end
    end
    if_op === nothing && return nothing

    # Get the condition SSAValue
    cond_val = if_op.condition
    cond_val isa SSAValue || return nothing

    # Find the condition expression in the body
    cond_entry = find_by_ssa(body.body, cond_val.id)
    cond_entry === nothing && return nothing
    cond_expr = cond_entry.stmt

    # Match the equality condition pattern: ===(BlockArg, upper_bound)
    matched = @match (cond_expr, body.args) begin
        for_equality_condition_pattern(iv, iv_idx, upper) => (iv, iv_idx, upper)
        _ => nothing
    end
    matched === nothing && return nothing
    iv_arg, iv_idx, upper_bound_raw = matched

    # Verify IV is in init_values range
    iv_idx > n_init_values && return nothing
    lower_bound = loop_op.init_values[iv_idx]

    # Determine which branch has ContinueOp (loop body) vs BreakOp (exit)
    then_term = if_op.then_region.terminator
    else_term = if_op.else_region.terminator

    continue_region = nothing
    break_region = nothing
    if then_term isa ContinueOp && else_term isa BreakOp
        continue_region = if_op.then_region
        break_region = if_op.else_region
    elseif else_term isa ContinueOp && then_term isa BreakOp
        continue_region = if_op.else_region
        break_region = if_op.then_region
    else
        return nothing
    end

    # For Julia's `for i in 1:n` pattern with === check, the step is always 1.
    # The step computation is in a different control flow path (not directly in body),
    # so we assume step=1 for UnitRange iteration.
    step = 1
    step_ssa_indices = Int[]

    # Try to find explicit step in body (for other patterns)
    step_result = find_step_in_block(body, iv_arg)
    if step_result !== nothing
        step_idx, step = step_result
        push!(step_ssa_indices, step_idx)
    end

    # Resolve upper_bound if it's a BlockArg
    function resolve_blockarg(arg)
        if arg isa BlockArg && arg.id <= n_init_values
            return loop_op.init_values[arg.id]
        end
        return arg
    end

    upper_bound = resolve_blockarg(upper_bound_raw)

    # Verify upper_bound is loop-invariant (step is constant 1, always invariant)
    is_loop_invariant(upper_bound, body, n_init_values) || return nothing

    # For Julia's inclusive range, we need upper_bound + 1 for exclusive ForOp semantics
    # This will be handled by inserting add_int in parent block

    # Separate non-IV init_values and identify the IV index for result types
    other_init_values = IRValue[]
    for (j, v) in enumerate(loop_op.init_values)
        j != iv_idx && push!(other_init_values, v)
    end

    # Find the IV's getfield in the parent block
    loop_ssa = SSAValue(current_key)
    getfields = find_getfields_for(parent_block, loop_ssa)
    iv_getfield_idx = nothing
    for gf in getfields
        if gf.field_idx == iv_idx
            iv_getfield_idx = gf.ssa_idx
            break
        end
    end

    # Build ForOp body from LoopOp body, excluding:
    # - The condition check (=== expression)
    # - The IfOp
    # - Step computations for the IV
    new_body = Block()
    new_body.args = [arg for arg in body.args if arg != iv_arg]

    cond_ssa_id = cond_val.id
    for (idx, entry) in body.body
        # Skip the condition check, IfOp, and step computations
        if idx == cond_ssa_id || idx == if_idx || idx in step_ssa_indices
            continue
        end
        push!(new_body, idx, entry.stmt, entry.typ)
    end

    # Get yield values from ContinueOp, excluding the IV
    cont_op = continue_region.terminator::ContinueOp
    yield_values = IRValue[]
    for (j, v) in enumerate(cont_op.values)
        j != iv_idx && j <= n_init_values && push!(yield_values, v)
    end
    new_body.terminator = ContinueOp(yield_values)

    # Create ForOp - upper bound will be adjusted by caller (add 1)
    for_op = ForOp(lower_bound, upper_bound, step, iv_arg, new_body, other_init_values)
    return (for_op, iv_getfield_idx, iv_idx, upper_bound)
end

"""
    find_step_in_block(block::Block, iv_arg::BlockArg) -> Union{Tuple{Int, Any}, Nothing}

Find the step expression `add_int(iv_arg, step)` in a block.
Returns (ssa_idx, step_value) or nothing.
"""
function find_step_in_block(block::Block, iv_arg::BlockArg)
    for (idx, entry) in block.body
        if !(entry.stmt isa ControlFlowOp)
            matched = @match (entry.stmt, iv_arg) begin
                for_step_pattern(step) => step
                _ => nothing
            end
            if matched !== nothing
                return (idx, matched)
            end
        end
    end
    return nothing
end

