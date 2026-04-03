# Loop promotion post-pass: LoopOp → WhileOp → ForOp
#
# After the core structurizer produces LoopOps (with ContinueOp/BreakOp),
# this pass recognizes higher-level patterns and promotes them:
#   1. LoopOp with condition-at-top → WhileOp (before/after regions)
#   2. WhileOp with counting pattern → ForOp (lower/upper/step/iv)
#
# Each promotion step remaps block arguments so each region owns its own
# arg namespace (MLIR's region ownership principle).

#=============================================================================
 Top-Level Promotion Pass
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

#=============================================================================
 LoopOp → WhileOp
=============================================================================#

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

    cond = if_op.condition
    stay_region = is_then_continue ? if_op.then_region : if_op.else_region
    exit_region = is_then_continue ? if_op.else_region : if_op.then_region

    # Only promote when cond=true → stay (standard while pattern).
    # Inverted patterns (cond=true → break) would require condition negation.
    if is_else_continue
        return nothing
    end

    # Standard pattern: cond=true → continue, cond=false → break
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
    for arg in body.args
        push!(before.args, arg)
    end

    # ConditionOp args = before block args (passed to after region when cond is true)
    cond_args = IRValue[arg for arg in before.args]
    before.terminator = ConditionOp(cond, cond_args)

    # After region: stay_region body + YieldOp with carried values (back to before)
    after = Block()
    arg_remap = Dict{Int, BlockArgument}()
    for arg in body.args
        after_arg = BlockArgument(alloc_arg!(ctx), arg.type)
        push!(after.args, after_arg)
        arg_remap[arg.id] = after_arg
    end
    for (sidx, sentry) in stay_region.body
        push!(after.body, (sidx, sentry.stmt, sentry.typ))
    end
    after.terminator = YieldOp(copy(continue_op.values))

    # Remap before-region block arg references to after-region block args.
    # Each region must reference its own args (MLIR's ownership principle).
    remap_block_args!(after, arg_remap)

    return WhileOp(before, after, loop.init_values)
end

#=============================================================================
 WhileOp → ForOp
=============================================================================#

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

    # Step must be loop-invariant (not defined inside the loop body)
    if step isa SSAValue && (haskey(op.after.body, step.id) || haskey(op.before.body, step.id))
        return (op, 0)
    end

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

    # Non-IV init values
    non_iv_inits = IRValue[]
    for (i, v) in enumerate(op.init_values)
        i == iv_pos && continue
        push!(non_iv_inits, v)
    end

    iv_arg = BlockArgument(alloc_arg!(ctx), iv_candidate.type)

    # Build ForOp body: copy after region, remove IV increment, remap args
    for_body = Block()
    arg_remap = Dict{Int, BlockArgument}()

    # Map after IV arg → ForOp's iv_arg
    arg_remap[after_iv_arg.id] = iv_arg
    # Also map before IV arg (in case of stale cross-scope refs)
    arg_remap[before_iv_arg.id] = iv_arg

    for (i, arg) in enumerate(after.args)
        i == iv_pos && continue
        for_arg = BlockArgument(alloc_arg!(ctx), arg.type)
        push!(for_body.args, for_arg)
        arg_remap[arg.id] = for_arg
        # Also map corresponding before arg
        if i <= length(before.args)
            arg_remap[before.args[i].id] = for_arg
        end
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

    # Remap all block arg references to ForOp's namespace
    remap_block_args!(for_body, arg_remap)
    step = remap_value(step, arg_remap)

    return (ForOp(lower, upper, step, iv_arg, for_body, non_iv_inits), iv_pos)
end

#=============================================================================
 Block Argument Remapping
=============================================================================#

"""
    remap_block_args!(block, remap::Dict{Int,BlockArgument})

Replace all BlockArgument references in a block's body and terminator.
Recurses into nested control flow ops. This ensures each region uses its
own block arg namespace (MLIR's "region owns its block arguments" principle).
"""
function remap_block_args!(block::Block, remap::Dict{Int, BlockArgument})
    isempty(remap) && return
    new_body = SSAMap()
    for (idx, entry) in block.body
        new_stmt = remap_value(entry.stmt, remap)
        push!(new_body, (idx, new_stmt, entry.typ))
    end
    block.body = new_body
    if block.terminator !== nothing
        block.terminator = remap_value(block.terminator, remap)
    end
end

function remap_value(@nospecialize(val), remap::Dict{Int, BlockArgument})
    if val isa BlockArgument
        return get(remap, val.id, val)
    elseif val isa Expr
        return Expr(val.head, Any[remap_value(a, remap) for a in val.args]...)
    elseif val isa PiNode
        return PiNode(remap_value(val.val, remap), val.typ)
    elseif val isa YieldOp
        return YieldOp(IRValue[remap_value(v, remap) for v in val.values])
    elseif val isa ContinueOp
        return ContinueOp(IRValue[remap_value(v, remap) for v in val.values])
    elseif val isa BreakOp
        return BreakOp(IRValue[remap_value(v, remap) for v in val.values])
    elseif val isa ConditionOp
        return ConditionOp(remap_value(val.condition, remap),
                           IRValue[remap_value(v, remap) for v in val.args])
    elseif val isa IfOp
        remap_block_args!(val.then_region, remap)
        remap_block_args!(val.else_region, remap)
        val.condition = remap_value(val.condition, remap)
        return val
    elseif val isa ForOp
        val.lower = remap_value(val.lower, remap)
        val.upper = remap_value(val.upper, remap)
        val.step = remap_value(val.step, remap)
        for (i, v) in enumerate(val.init_values)
            val.init_values[i] = remap_value(v, remap)
        end
        remap_block_args!(val.body, remap)
        return val
    elseif val isa WhileOp
        for (i, v) in enumerate(val.init_values)
            val.init_values[i] = remap_value(v, remap)
        end
        remap_block_args!(val.before, remap)
        remap_block_args!(val.after, remap)
        return val
    elseif val isa LoopOp
        for (i, v) in enumerate(val.init_values)
            val.init_values[i] = remap_value(v, remap)
        end
        remap_block_args!(val.body, remap)
        return val
    elseif val isa ReturnNode
        isdefined(val, :val) || return val
        new_v = remap_value(val.val, remap)
        return new_v === val.val ? val : ReturnNode(new_v)
    else
        return val
    end
end
