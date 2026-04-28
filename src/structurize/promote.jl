# Loop promotion post-pass: LoopOp → WhileOp → ForOp
#
# After the core structurizer produces LoopOps (with ContinueOp/BreakOp),
# this pass recognizes higher-level patterns and promotes them:
#   1. LoopOp with iteration protocol exit → ForOp (direct, via simplify+detect)
#   2. LoopOp with condition-at-top → WhileOp (before/after regions)
#   3. WhileOp with counting pattern → ForOp (lower/upper/step/iv)
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
    # Track ForOp promotions: loop_ssa_idx → (removed_positions, ForOp, carry_redirect)
    for_promotions = Dict{Int, Tuple{Vector{Int}, ForOp, Dict{Int,Int}}}()

    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa LoopOp
            # Recursively promote inner loops first
            promote_loops!(stmt.body, ctx)
            # Try direct LoopOp → ForOp (handles iteration protocol patterns)
            result, removed, redirect = try_promote_for_from_loop(stmt, idx, block, new_body, ctx)
            if result isa ForOp
                for_promotions[idx] = (removed, result, redirect)
                carry_types = Any[t for (i, t) in enumerate(entry.typ.parameters) if i ∉ removed]
                push!(new_body, (idx, result, Tuple{carry_types...}, entry.flag))
            else
                # Fall back to existing path: LoopOp → WhileOp → ForOp
                promoted = try_promote_while(stmt, ctx)
                if promoted !== nothing
                    result2, iv_pos = try_promote_for(promoted, idx, block, new_body, ctx)
                    if result2 isa ForOp && iv_pos > 0
                        for_promotions[idx] = ([iv_pos], result2, Dict{Int,Int}())
                        carry_types = Any[t for (i, t) in enumerate(entry.typ.parameters) if i != iv_pos]
                        push!(new_body, (idx, result2, Tuple{carry_types...}, entry.flag))
                    else
                        push!(new_body, (idx, result2, entry.typ, entry.flag))
                    end
                else
                    push!(new_body, (idx, stmt, entry.typ, entry.flag))
                end
            end
        elseif stmt isa Expr && stmt.head === :call && stmt.args[1] === Core.getfield &&
               stmt.args[2] isa SSAValue && haskey(for_promotions, stmt.args[2].id)
            # Fix getfield for ForOp: removed positions → upper bound or redirect, others → adjusted index
            loop_ssa = stmt.args[2].id
            field_idx = stmt.args[3]::Int
            removed, for_op, redirect = for_promotions[loop_ssa]
            if field_idx ∈ removed
                target_pos = get(redirect, field_idx, 0)
                if target_pos > 0
                    # Duplicate carry → redirect to surviving carry's adjusted index
                    adjusted = target_pos - count(p -> p < target_pos, removed)
                    new_gf = Expr(:call, Core.getfield, SSAValue(loop_ssa), adjusted)
                    push!(new_body, (idx, new_gf, entry.typ, entry.flag))
                else
                    push!(new_body, (idx, for_op.upper, entry.typ, entry.flag))
                end
            else
                adjusted = field_idx - count(p -> p < field_idx, removed)
                new_gf = Expr(:call, Core.getfield, SSAValue(loop_ssa), adjusted)
                push!(new_body, (idx, new_gf, entry.typ, entry.flag))
            end
        elseif stmt isa ControlFlowOp
            for b in blocks(stmt)
                promote_loops!(b, ctx)
            end
            push!(new_body, (idx, stmt, entry.typ, entry.flag))
        else
            push!(new_body, (idx, stmt, entry.typ, entry.flag))
        end
    end
    block.body = new_body
end

#=============================================================================
 LoopOp → ForOp (direct, for iteration protocol patterns)
=============================================================================#

"""
Simplify a LoopOp body that has the iteration protocol exit pattern:
  inner_if(cond) → done-flag → getfields → not_int → outer_if(continue/break)
into a single IfOp:
  if(cond) { break } else { body; continue }
Returns a new Block with the simplified body, or nothing if the pattern doesn't match.
The original body is not modified.
"""
function simplify_loop_exit(body::Block)
    length(body.body) < 2 && return nothing

    # Find the last IfOp (outer exit dispatch)
    outer_pos = length(body.body.ssa_idxes)
    outer_idx = body.body.ssa_idxes[outer_pos]
    outer = body.body.stmts[outer_pos]
    outer isa IfOp || return nothing

    # Outer must have ContinueOp + BreakOp branches
    then_t = outer.then_region.terminator
    else_t = outer.else_region.terminator
    has_cb = (then_t isa ContinueOp && else_t isa BreakOp) ||
             (then_t isa BreakOp && else_t isa ContinueOp)
    has_cb || return nothing

    # Trace outer condition backward: should be not_int(getfield(%inner, k))
    # or getfield(%inner, k) directly
    cond = outer.condition
    inverted = false
    if cond isa SSAValue
        cond_entry = get(body.body, cond.id, nothing)
        if cond_entry !== nothing && cond_entry.stmt isa Expr &&
           cond_entry.stmt.head === :call && length(cond_entry.stmt.args) == 2
            func = cond_entry.stmt.args[1]
            if func isa GlobalRef && func.name === :not_int
                cond = cond_entry.stmt.args[2]
                inverted = true
            end
        end
    end

    # cond should now be getfield(%inner_result, flag_pos)
    cond isa SSAValue || return nothing
    flag_entry = get(body.body, cond.id, nothing)
    flag_entry === nothing && return nothing
    flag_stmt = flag_entry.stmt
    (flag_stmt isa Expr && flag_stmt.head === :call &&
     length(flag_stmt.args) == 3 && flag_stmt.args[1] === Core.getfield) || return nothing
    inner_result = flag_stmt.args[2]
    inner_result isa SSAValue || return nothing
    flag_pos = flag_stmt.args[3]::Int

    # inner_result should be an IfOp in the body
    inner_entry = get(body.body, inner_result.id, nothing)
    inner_entry === nothing && return nothing
    inner = inner_entry.stmt
    inner isa IfOp || return nothing

    # Verify: inner yield[flag_pos] is boolean constant in both branches
    inner.then_region.terminator isa YieldOp || return nothing
    inner.else_region.terminator isa YieldOp || return nothing
    then_yield = inner.then_region.terminator::YieldOp
    else_yield = inner.else_region.terminator::YieldOp
    flag_pos <= length(then_yield.values) && flag_pos <= length(else_yield.values) || return nothing
    then_flag = then_yield.values[flag_pos]
    else_flag = else_yield.values[flag_pos]
    (then_flag isa Bool && else_flag isa Bool && then_flag != else_flag) || return nothing

    # Determine which inner branch is "done" (flag=true) and which is "not done"
    done_yield = then_flag ? then_yield : else_yield
    cont_yield = then_flag ? else_yield : then_yield
    done_body_region = then_flag ? inner.then_region : inner.else_region
    cont_body_region = then_flag ? inner.else_region : inner.then_region

    # Determine which outer branch is "continue" and which is "break"
    # inverted=false: outer condition = flag, so true=done → break
    # inverted=true:  outer condition = not_int(flag), so true=not_done → continue
    if inverted
        cont_term = then_t
        break_term = else_t
    else
        break_term = then_t
        cont_term = else_t
    end
    cont_term isa ContinueOp || return nothing

    # Build getfield→inner_yield substitution maps
    cont_subs = Dict{Int, Any}()
    break_subs = Dict{Int, Any}()
    for (sidx, sentry) in body.body
        s = sentry.stmt
        s isa Expr || continue
        s.head === :call && length(s.args) == 3 && s.args[1] === Core.getfield || continue
        s.args[2] isa SSAValue && s.args[2].id == inner_result.id || continue
        gf_pos = s.args[3]::Int
        gf_pos <= length(cont_yield.values) || continue
        cont_subs[sidx] = cont_yield.values[gf_pos]
        break_subs[sidx] = done_yield.values[gf_pos]
    end

    subst_val(v, subs) = v isa SSAValue && haskey(subs, v.id) ? subs[v.id] : v
    cont_values = IRValue[subst_val(v, cont_subs) for v in cont_term.values]
    break_values = IRValue[subst_val(v, break_subs) for v in break_term.values]

    # Build merged IfOp: inner condition true → done → break, false → continue
    merged_then = Block()
    for (sidx, sentry) in done_body_region.body
        push!(merged_then.body, (sidx, sentry.stmt, sentry.typ, sentry.flag))
    end
    merged_then.terminator = BreakOp(break_values)

    merged_else = Block()
    for (sidx, sentry) in cont_body_region.body
        push!(merged_else.body, (sidx, sentry.stmt, sentry.typ, sentry.flag))
    end
    merged_else.terminator = ContinueOp(cont_values)

    merged_if = IfOp(inner.condition, merged_then, merged_else)

    # Build new Block with simplified body (original is not modified)
    result = Block()
    for arg in body.args
        push!(result.args, arg)
    end
    for (sidx, sentry) in body.body
        sidx == inner_result.id && break
        push!(result.body, (sidx, sentry.stmt, sentry.typ, sentry.flag))
    end
    push!(result.body, (outer_idx, merged_if, Tuple{}))
    return result
end

"""Check if an SSA value is referenced in a block's body (after `after_idx`) or terminator."""
function _ssa_used_in_block(ssa::SSAValue, after_idx::Int, block::Block)
    past = false
    for (sidx, sentry) in block.body
        if sidx == after_idx
            past = true
            continue
        end
        past || continue
        _refs_ssa(sentry.stmt, ssa) && return true
    end
    block.terminator !== nothing && _refs_ssa(block.terminator, ssa) && return true
    return false
end

function _refs_ssa(@nospecialize(val), ssa::SSAValue)
    val === ssa && return true
    if val isa Expr
        return any(a -> _refs_ssa(a, ssa), val.args)
    elseif val isa YieldOp
        return any(v -> v === ssa, val.values)
    elseif val isa ContinueOp
        return any(v -> v === ssa, val.values)
    elseif val isa BreakOp
        return any(v -> v === ssa, val.values)
    elseif val isa ReturnNode
        return isdefined(val, :val) && val.val === ssa
    end
    return false
end

"""
Try to promote a LoopOp directly to ForOp by detecting the iteration protocol
counting pattern. Works on LoopOps that have been simplified by simplify_loop_exit!.
Returns (ForOp, removed_positions) or (loop, Int[]) if promotion fails.
"""
function try_promote_for_from_loop(loop::LoopOp, idx::Int, parent_block::Block,
                                    new_body::SSAMap, ctx::StructurizeCtx)
    # Try simplifying the exit structure (returns new Block, doesn't modify original)
    body = simplify_loop_exit(loop.body)
    body === nothing && return (loop, Int[], Dict{Int,Int}())

    # After simplification: body should end with IfOp(cond, break, continue) or vice versa
    isempty(body.body) && return (loop, Int[], Dict{Int,Int}())
    last_stmt = body.body.stmts[end]
    last_stmt isa IfOp || return (loop, Int[], Dict{Int,Int}())
    if_op = last_stmt

    then_t = if_op.then_region.terminator
    else_t = if_op.else_region.terminator

    # Determine break/continue branches (either polarity)
    if then_t isa BreakOp && else_t isa ContinueOp
        break_op, continue_op = then_t, else_t
        cont_region = if_op.else_region
    elseif then_t isa ContinueOp && else_t isa BreakOp
        continue_op, break_op = then_t, else_t
        cont_region = if_op.then_region
    else
        return (loop, Int[], Dict{Int,Int}())
    end

    # Condition must be a comparison: ===, slt_int, sle_int on block_arg vs bound
    cond_val = if_op.condition
    cond_val isa SSAValue || return (loop, Int[], Dict{Int,Int}())
    cond_entry = get(body.body, cond_val.id, nothing)
    cond_entry === nothing && return (loop, Int[], Dict{Int,Int}())
    cond_expr = cond_entry.stmt
    (cond_expr isa Expr && cond_expr.head === :call && length(cond_expr.args) >= 3) ||
        return (loop, Int[], Dict{Int,Int}())

    func = cond_expr.args[1]
    iv_candidate = cond_expr.args[2]
    bound = cond_expr.args[3]

    # Only handle === with break-on-true (the iteration protocol pattern).
    # slt_int/sle_int patterns are handled by the WhileOp→ForOp path.
    is_eq = (func isa GlobalRef && func.name === :(===)) || func === :(===)
    (is_eq && then_t isa BreakOp) || return (loop, Int[], Dict{Int,Int}())

    iv_candidate isa BlockArgument || return (loop, Int[], Dict{Int,Int}())
    iv_pos = findfirst(a -> a.id == iv_candidate.id, body.args)
    iv_pos === nothing && return (loop, Int[], Dict{Int,Int}())

    # Find step: add_int(iv_arg, step) in the continue branch at iv_pos
    iv_pos <= length(continue_op.values) || return (loop, Int[], Dict{Int,Int}())
    step_val = continue_op.values[iv_pos]
    step = nothing
    step_ssa = nothing
    if step_val isa SSAValue
        step_entry = get(cont_region.body, step_val.id, nothing)
        if step_entry !== nothing
            s = step_entry.stmt
            if s isa Expr && s.head === :call && length(s.args) >= 3
                sfunc = s.args[1]
                if sfunc isa GlobalRef && sfunc.name === :add_int &&
                   s.args[2] isa BlockArgument && s.args[2].id == iv_candidate.id
                    step = s.args[3]
                    step_ssa = step_val.id
                end
            end
        end
    end
    step === nothing && return (loop, Int[], Dict{Int,Int}())

    # ForOp requires positive step (ascending loops only)
    step isa Integer && step < 0 && return (loop, Int[], Dict{Int,Int}())

    # Step and bound must be loop-invariant
    if step isa SSAValue && haskey(body.body, step.id)
        return (loop, Int[], Dict{Int,Int}())
    end
    if bound isa BlockArgument && any(a -> a.id == bound.id, body.args)
        return (loop, Int[], Dict{Int,Int}())
    end

    # Shadow IV detection: other args whose continue value is the same SSA as
    # the IV's continue value (they track the same induction variable)
    removed = Int[iv_pos]
    for (i, arg) in enumerate(body.args)
        i == iv_pos && continue
        i <= length(continue_op.values) || continue
        continue_op.values[i] == step_val || continue
        push!(removed, i)
    end

    # Duplicate carry detection: among non-removed positions, find args with
    # identical continue values. Remove the Undef-initialized duplicate and
    # redirect its getfield to the real carry.
    carry_redirect = Dict{Int, Int}()  # removed_pos → surviving_pos
    seen_continues = Dict{Any, Int}()  # continue_value → first non-removed pos
    for i in 1:length(body.args)
        i ∈ removed && continue
        i <= length(continue_op.values) || continue
        cv = continue_op.values[i]
        prev = get(seen_continues, cv, 0)
        if prev == 0
            seen_continues[cv] = i
        else
            if loop.init_values[i] isa Undef && !(loop.init_values[prev] isa Undef)
                push!(removed, i)
                carry_redirect[i] = prev
            elseif loop.init_values[prev] isa Undef && !(loop.init_values[i] isa Undef)
                push!(removed, prev)
                carry_redirect[prev] = i
                seen_continues[cv] = i
            end
        end
    end
    sort!(removed)

    # Safety: for non-removed positions where break != continue,
    # verify no getfield at that position is actually used in the parent block.
    # Pre-scan parent block once to map getfield positions → SSA indices.
    gf_ssa_for_pos = Dict{Int, Int}()  # loop result position → getfield SSA idx
    for (pidx, pentry) in parent_block.body
        s = pentry.stmt
        s isa Expr || continue
        s.head === :call && length(s.args) == 3 && s.args[1] === Core.getfield || continue
        s.args[2] isa SSAValue && s.args[2].id == idx || continue
        gf_ssa_for_pos[s.args[3]::Int] = pidx
    end
    for (i, arg) in enumerate(body.args)
        i ∈ removed && continue
        i <= length(break_op.values) && i <= length(continue_op.values) || continue
        break_op.values[i] == continue_op.values[i] && continue
        gf_idx = get(gf_ssa_for_pos, i, 0)
        gf_idx == 0 && continue
        _ssa_used_in_block(SSAValue(gf_idx), gf_idx, parent_block) && return (loop, Int[], Dict{Int,Int}())
    end

    # --- Build ForOp ---
    lower = loop.init_values[iv_pos]
    # For ===: body runs for iv = init...bound inclusive, exclusive upper = bound + step
    adj_ssa = alloc_ssa!(ctx)
    anchor_line!(ctx, adj_ssa, cond_val.id)
    upper_type = iv_candidate.type
    add_expr = Expr(:call, GlobalRef(Base, :add_int), bound, step)
    push!(new_body, (adj_ssa, add_expr, upper_type))
    upper = SSAValue(adj_ssa)

    iv_arg = BlockArgument(alloc_arg!(ctx), iv_candidate.type)
    for_body = Block()
    arg_remap = Dict{Int, BlockArgument}()

    # Map IV and shadow IVs to ForOp's iv_arg (skip duplicate carries)
    for r in removed
        haskey(carry_redirect, r) && continue
        arg_remap[body.args[r].id] = iv_arg
    end

    # Non-IV, non-shadow, non-duplicate args get fresh BlockArguments
    non_iv_inits = IRValue[]
    for (i, arg) in enumerate(body.args)
        i ∈ removed && continue
        for_arg = BlockArgument(alloc_arg!(ctx), arg.type)
        push!(for_body.args, for_arg)
        arg_remap[arg.id] = for_arg
        push!(non_iv_inits, loop.init_values[i])
    end

    # Map duplicate carries to their surviving equivalent's BlockArgument
    for (dup_pos, surv_pos) in carry_redirect
        arg_remap[body.args[dup_pos].id] = arg_remap[body.args[surv_pos].id]
    end

    # Body: stmts before the exit IfOp + continue branch stmts (minus IV increment)
    last_idx = body.body.ssa_idxes[end]
    for (sidx, sentry) in body.body
        sidx == last_idx && break
        push!(for_body.body, (sidx, sentry.stmt, sentry.typ, sentry.flag))
    end
    for (sidx, sentry) in cont_region.body
        step_ssa !== nothing && sidx == step_ssa && continue  # skip IV increment
        push!(for_body.body, (sidx, sentry.stmt, sentry.typ, sentry.flag))
    end

    # ContinueOp with non-IV, non-shadow values
    cont_values = IRValue[]
    for (i, v) in enumerate(continue_op.values)
        i ∈ removed && continue
        push!(cont_values, v)
    end
    for_body.terminator = ContinueOp(cont_values)

    remap_block_args!(for_body, arg_remap)
    step = remap_value(step, arg_remap)

    return (ForOp(lower, upper, step, iv_arg, for_body, non_iv_inits), removed, carry_redirect)
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
        push!(before.body, (sidx, sentry.stmt, sentry.typ, sentry.flag))
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
        push!(after.body, (sidx, sentry.stmt, sentry.typ, sentry.flag))
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

    # Look for: condition is slt_int/sle_int on a block arg vs loop-invariant bound
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

    # Check condition function (=== is not a counting pattern; handled by Path A)
    is_slt = func isa GlobalRef && func.name in (:slt_int, :ult_int)
    is_sle = func isa GlobalRef && func.name === :sle_int
    (is_slt || is_sle) || return (op, 0)

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

    # ForOp requires positive step (ascending loops only)
    step isa Integer && step < 0 && return (op, 0)

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
    is_inclusive = is_sle

    # Exclusive upper bound: add 1 if inclusive
    if is_inclusive
        adj_ssa = alloc_ssa!(ctx)
        anchor_line!(ctx, adj_ssa, cond_val.id)
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
        push!(for_body.body, (sidx, sentry.stmt, sentry.typ, sentry.flag))
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
        push!(new_body, (idx, new_stmt, entry.typ, entry.flag))
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
