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

"""Count `BreakOp` terminators reachable inside this loop body, descending into
`IfOp` arms but NOT into nested loops (whose breaks are their own). A counted/
condition loop has exactly one — its iteration-exit break; a second one is a
*secondary* dynamic exit (an early `break`/`return` reached mid-body) that `ForOp`/
`WhileOp` cannot represent (their iteration is fixed), so such a loop must stay a
`LoopOp`. Promoting it produced a `ForOp` body with a stray `BreakOp` whose exit
placeholder leaked at unstructurize — a crash; this guard prevents it."""
function count_breaks(block::Block)
    n = block.terminator isa BreakOp ? 1 : 0
    for (_, e) in block.body
        e.stmt isa IfOp || continue
        n += count_breaks(e.stmt.then_region) + count_breaks(e.stmt.else_region)
    end
    return n
end

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
        if stmt isa LoopOp && count_breaks(stmt.body) > 1
            # Secondary dynamic exit (e.g. an early break/return alongside the
            # iteration-exit break): only the general LoopOp can represent it.
            promote_loops!(stmt.body, ctx)
            push!(new_body, (idx, stmt, entry.type, entry.flag))
        elseif stmt isa LoopOp
            # Recursively promote inner loops first
            promote_loops!(stmt.body, ctx)
            # Try direct LoopOp → ForOp (handles iteration protocol patterns)
            result, removed, redirect = try_promote_for_from_loop(stmt, idx, block, new_body, ctx)
            if result isa ForOp
                for_promotions[idx] = (removed, result, redirect)
                carry_types = Any[t for (i, t) in enumerate(entry.type.parameters) if i ∉ removed]
                push!(new_body, (idx, result, Tuple{carry_types...}, entry.flag))
            else
                # Fall back to existing path: LoopOp → WhileOp → ForOp
                promoted = try_promote_while(stmt, ctx)
                if promoted !== nothing
                    result2, removed2 = try_promote_for(promoted, idx, block, new_body, ctx)
                    if result2 isa ForOp
                        if isempty(removed2)
                            # IV kept as an ordinary carry because it escapes (PLAN7
                            # Phase 1): arity/order are unchanged, so post-loop
                            # getfields read it directly — no for_promotions entry and
                            # no getfield rewrite. The empty-case value comes out right
                            # for free from carried-value semantics (empty ⇒ init).
                            push!(new_body, (idx, result2, entry.type, entry.flag))
                        else
                            for_promotions[idx] = (removed2, result2, Dict{Int,Int}())
                            carry_types = Any[t for (i, t) in enumerate(entry.type.parameters) if i ∉ removed2]
                            push!(new_body, (idx, result2, Tuple{carry_types...}, entry.flag))
                        end
                    else
                        push!(new_body, (idx, result2, entry.type, entry.flag))
                    end
                else
                    push!(new_body, (idx, stmt, entry.type, entry.flag))
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
                    push!(new_body, (idx, new_gf, entry.type, entry.flag))
                else
                    # `upper` alias for a removed IV/shadow position. Since PLAN7
                    # keeps every *escaping* removed position as a real carry, this
                    # branch is reachable only for a provably-dead getfield (the
                    # IV-escape gate returned false), so the alias is never observed.
                    @assert !_ssa_used_in_block(SSAValue(idx), idx, block) "escaping removed position aliased to upper (PLAN7 invariant violated)"
                    push!(new_body, (idx, for_op.upper, entry.type, entry.flag))
                end
            else
                adjusted = field_idx - count(p -> p < field_idx, removed)
                new_gf = Expr(:call, Core.getfield, SSAValue(loop_ssa), adjusted)
                push!(new_body, (idx, new_gf, entry.type, entry.flag))
            end
        elseif stmt isa ControlFlowOp
            for b in blocks(stmt)
                promote_loops!(b, ctx)
            end
            push!(new_body, (idx, stmt, entry.type, entry.flag))
        else
            push!(new_body, (idx, stmt, entry.type, entry.flag))
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
        push!(merged_then.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
    end
    merged_then.terminator = BreakOp(break_values)

    merged_else = Block()
    for (sidx, sentry) in cont_body_region.body
        push!(merged_else.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
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
        push!(result.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
    end
    push!(result.body, (outer_idx, merged_if, Tuple{}))
    return result
end

"""Does a post-loop read of the loop result's `pos`-th field survive in the parent
block? A `ForOp` does not carry its induction variable as a result — it is implicit
in the range — so `promote_loops!` aliases any post-loop `getfield` at the IV
position to the loop's exclusive `upper` bound. That alias equals the final IV only
when the loop body ran (`for i in lo:hi` exits with `i == hi`); for an *empty* loop
(init ≥ bound, zero trips) the final IV is the **init** (`lower`), not `upper`, so
the alias silently returns the bound (ISSUES.md #3). When the IV escapes we must
therefore *not* promote to `ForOp`; the `WhileOp` form carries the IV as a genuine
result and stays correct for the empty case. A true counted `for i in lo:hi` never
reads `i` after the loop (Julia scopes it), so this gate does not demote real
counted loops — only `while`-shaped loops whose tested value is read afterwards."""
function loop_result_pos_escapes(loop_idx::Int, pos::Int, parent_block::Block)
    for (pidx, pentry) in parent_block.body
        s = pentry.stmt
        s isa Expr || continue
        s.head === :call && length(s.args) == 3 && s.args[1] === Core.getfield || continue
        s.args[2] isa SSAValue && s.args[2].id == loop_idx || continue
        s.args[3]::Int == pos || continue
        _ssa_used_in_block(SSAValue(pidx), pidx, parent_block) && return true
    end
    return false
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

"""Deep `_refs_ssa`: also recurses into nested control-flow regions and a
`Block`, so a use buried in a nested IfOp/loop body still counts."""
function _refs_ssa_deep(@nospecialize(val), ssa::SSAValue)
    if val isa IfOp
        return _refs_ssa(val.condition, ssa) ||
               _refs_ssa_deep(val.then_region, ssa) || _refs_ssa_deep(val.else_region, ssa)
    elseif val isa ForOp
        return _refs_ssa(val.lower, ssa) || _refs_ssa(val.upper, ssa) || _refs_ssa(val.step, ssa) ||
               any(v -> _refs_ssa(v, ssa), val.init_values) || _refs_ssa_deep(val.body, ssa)
    elseif val isa WhileOp
        return any(v -> _refs_ssa(v, ssa), val.init_values) ||
               _refs_ssa_deep(val.before, ssa) || _refs_ssa_deep(val.after, ssa)
    elseif val isa LoopOp
        return any(v -> _refs_ssa(v, ssa), val.init_values) || _refs_ssa_deep(val.body, ssa)
    elseif val isa Block
        for (_, e) in val.body
            _refs_ssa_deep(e.stmt, ssa) && return true
        end
        return val.terminator !== nothing && _refs_ssa_deep(val.terminator, ssa)
    else
        return _refs_ssa(val, ssa)
    end
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

    # IV-escape gate (ISSUES.md #3 / PLAN7 Phase 2): removed positions (the IV and
    # its value#1 shadows) would otherwise be aliased to `upper` post-loop — wrong
    # for an empty loop, whose final IV is the init. Rather than decline the whole
    # promotion, *partition* `removed`: any escaping position becomes a real kept
    # carry (read back normally), while the rest stay removed (their `upper` alias
    # is then provably dead). Duplicate-carry redirects stay removed (an Undef-init
    # dup is not a meaningful escaping value; it is folded into its survivor).
    kept = Int[]
    for r in removed
        haskey(carry_redirect, r) && continue
        loop_result_pos_escapes(idx, r, parent_block) && push!(kept, r)
    end
    removed = setdiff(removed, kept)   # run before any count(p<…, removed)/carry_types

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

    # Map (still-)removed IV / shadow IVs to ForOp's iv_arg (skip duplicate carries)
    for r in removed
        haskey(carry_redirect, r) && continue
        arg_remap[body.args[r].id] = iv_arg
    end

    # Retained carries — genuine carries AND kept escaping IV/shadows (no longer in
    # `removed`) — get fresh BlockArguments in original index order, each with its
    # own init. A kept escaping IV/shadow is the current IV *in-body* (e.g. the same
    # value an `acc += i` reads), so its in-body uses must resolve to `iv_arg`; its
    # fresh for-arg is then a write-only carry slot that only exposes the post-loop
    # result. A genuine carry maps its body uses to its own for-arg as usual.
    non_iv_inits = IRValue[]
    for (i, arg) in enumerate(body.args)
        i ∈ removed && continue
        for_arg = BlockArgument(alloc_arg!(ctx), arg.type)
        push!(for_body.args, for_arg)
        arg_remap[arg.id] = (i ∈ kept) ? iv_arg : for_arg
        push!(non_iv_inits, loop.init_values[i])
    end

    # Map duplicate carries to their surviving equivalent's BlockArgument
    for (dup_pos, surv_pos) in carry_redirect
        arg_remap[body.args[dup_pos].id] = arg_remap[body.args[surv_pos].id]
    end

    # ContinueOp values. A kept escaping position must carry `iv_arg` itself — NOT
    # its lifted continue, which is the *advanced* value `iv+step` (the iterate
    # protocol advances before re-checking, so that continue equals `upper`, the
    # post-loop bound). Carrying `iv_arg` makes the kept carry's last value the last
    # in-body IV (`upper − step`), matching the LoopOp's break (the pre-advance
    # current value); the empty range is guarded by the outer `if`, so the init is
    # only read when the loop ran (PLAN7 §3 — the research answer is wrong here).
    cont_values = IRValue[]
    for (i, v) in enumerate(continue_op.values)
        i ∈ removed && continue
        push!(cont_values, i ∈ kept ? iv_arg : v)
    end

    # The IV increment (`step_ssa = iv + step`) is implicit in the range. Kept
    # carries reference `iv_arg`, not the increment, so the statement is needed only
    # if some other retained body stmt or surviving carried value reads it. Keep it
    # iff referenced — a dead increment is harmless, a missing one dangles.
    last_idx = body.body.ssa_idxes[end]
    incr_used = false
    if step_ssa !== nothing
        for v in cont_values
            v isa SSAValue && v.id == step_ssa && (incr_used = true; break)
        end
        if !incr_used
            for (sidx, sentry) in body.body
                sidx == last_idx && break
                _refs_ssa_deep(sentry.stmt, SSAValue(step_ssa)) && (incr_used = true; break)
            end
        end
        if !incr_used
            for (sidx, sentry) in cont_region.body
                sidx == step_ssa && continue
                _refs_ssa_deep(sentry.stmt, SSAValue(step_ssa)) && (incr_used = true; break)
            end
        end
    end

    # Body: stmts before the exit IfOp + continue branch stmts (minus dead increment)
    for (sidx, sentry) in body.body
        sidx == last_idx && break
        push!(for_body.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
    end
    for (sidx, sentry) in cont_region.body
        step_ssa !== nothing && sidx == step_ssa && !incr_used && continue  # drop dead IV increment
        push!(for_body.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
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
        push!(before.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
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
        push!(after.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
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
Returns `(promoted_op, removed)` where `removed::Vector{Int}` lists the loop-result
positions the ForOp dropped (the caller adjusts post-loop `getfield`s accordingly):
- `(ForOp, [iv_pos])` — the IV was removed (the usual case; it is implicit in the range).
- `(ForOp, Int[])` — the IV escapes, so it is **kept** as an ordinary carry (PLAN7
  Phase 1): the result arity/order match the original WhileOp and the empty (zero-trip)
  case reads back the init, not the bound. No position is removed.
- `(op, Int[])` with `op` still a WhileOp — not promoted.
"""
function try_promote_for(op, idx::Int, parent_block::Block, new_body::SSAMap,
                          ctx::StructurizeCtx)
    op isa WhileOp || return (op, Int[])

    # Look for: condition is slt_int/sle_int on a block arg vs loop-invariant bound
    before = op.before
    before.terminator isa ConditionOp || return (op, Int[])
    cond_op = before.terminator

    # Find the condition expression
    cond_val = cond_op.condition
    cond_val isa SSAValue || return (op, Int[])
    cond_entry = get(before.body, cond_val.id, nothing)
    cond_entry === nothing && return (op, Int[])
    cond_expr = cond_entry.stmt
    cond_expr isa Expr && cond_expr.head === :call || return (op, Int[])
    length(cond_expr.args) >= 3 || return (op, Int[])

    func = cond_expr.args[1]
    iv_candidate = cond_expr.args[2]
    bound = cond_expr.args[3]

    # Check condition function (=== is not a counting pattern; handled by Path A)
    is_slt = func isa GlobalRef && func.name in (:slt_int, :ult_int)
    is_sle = func isa GlobalRef && func.name === :sle_int
    (is_slt || is_sle) || return (op, Int[])

    # IV must be a block argument
    iv_candidate isa BlockArgument || return (op, Int[])

    # Find IV's position in args
    iv_pos = findfirst(a -> a.id == iv_candidate.id, before.args)
    iv_pos === nothing && return (op, Int[])

    # IV-escape gate (ISSUES.md #3 / PLAN7): a ForOp does not carry its IV as a
    # result. If the IV is read after the loop, do NOT drop it — keep it as an
    # ordinary carry (`keep_iv`) so the post-loop read is a normal result, correct
    # for both the empty (init) and non-empty (last continue = upper) cases. When
    # the IV does not escape, drop it as before (it is redundant with the range).
    keep_iv = loop_result_pos_escapes(idx, iv_pos, parent_block)

    # Find step: look in the after region for add_int(iv_arg, step)
    after = op.after
    iv_pos <= length(after.args) || return (op, Int[])
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
    step === nothing && return (op, Int[])

    # ForOp requires positive step (ascending loops only)
    step isa Integer && step < 0 && return (op, Int[])

    # Step must be loop-invariant (not defined inside the loop body)
    if step isa SSAValue && (haskey(op.after.body, step.id) || haskey(op.before.body, step.id))
        return (op, Int[])
    end

    # Bound must be loop-invariant (not a block arg of this loop)
    if bound isa BlockArgument && any(a -> a.id == bound.id, before.args)
        return (op, Int[])
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

    # Carry init values. When the IV escapes (`keep_iv`) it rides as an ordinary
    # carry, so its init (`lower`) is kept in place and the arity/order match the
    # original WhileOp; otherwise the IV position is dropped (implicit in the range).
    carry_inits = IRValue[]
    for (i, v) in enumerate(op.init_values)
        (i == iv_pos && !keep_iv) && continue
        push!(carry_inits, v)
    end

    iv_arg = BlockArgument(alloc_arg!(ctx), iv_candidate.type)

    # Build ForOp body: copy after region, remove IV increment, remap args
    for_body = Block()
    arg_remap = Dict{Int, BlockArgument}()

    for (i, arg) in enumerate(after.args)
        (i == iv_pos && !keep_iv) && continue
        for_arg = BlockArgument(alloc_arg!(ctx), arg.type)
        push!(for_body.args, for_arg)
        arg_remap[arg.id] = for_arg
        # Also map corresponding before arg
        if i <= length(before.args)
            arg_remap[before.args[i].id] = for_arg
        end
    end

    # In-body IV references always resolve to the implicit induction variable
    # (`iv_arg`), overriding the write-only carry slot the kept-IV loop just mapped
    # above: the kept carry is computed (continue = the increment) but never read.
    arg_remap[after_iv_arg.id] = iv_arg
    arg_remap[before_iv_arg.id] = iv_arg

    # The IV increment (`carried_val = iv + step`) is implicit in a ForOp, so it
    # is normally dropped. But if another body statement or a surviving carried
    # value reads it — e.g. `s += k` where `k` is the post-increment IV, or the
    # kept-IV carry whose continue *is* the increment — it must stay, remapped
    # below to read the ForOp's induction variable; dropping it then left a
    # dangling SSA reference (`%k used but not defined`).
    incr_used = keep_iv
    if !incr_used && carried_val isa SSAValue
        for (sidx, sentry) in after.body
            sidx == carried_val.id && continue
            if _refs_ssa_deep(sentry.stmt, carried_val); incr_used = true; break; end
        end
        if !incr_used && after.terminator isa YieldOp
            for (i, v) in enumerate(after.terminator.values)
                i != iv_pos && v isa SSAValue && v.id == carried_val.id && (incr_used = true; break)
            end
        end
    end

    for (sidx, sentry) in after.body
        # Skip the IV increment statement, unless something else reads it.
        if carried_val isa SSAValue && sidx == carried_val.id && !incr_used
            continue
        end
        push!(for_body.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
    end

    # ContinueOp carried values. At `iv_pos` (when kept) this is `carried_val`, the
    # increment SSA = `iv + step`; its last value is `upper` (non-empty) so the kept
    # carry's result matches `while`-counted post-increment semantics.
    cont_values = IRValue[]
    if after.terminator isa YieldOp
        for (i, v) in enumerate(after.terminator.values)
            (i == iv_pos && !keep_iv) && continue
            push!(cont_values, v)
        end
    end
    for_body.terminator = ContinueOp(cont_values)

    # Remap all block arg references to ForOp's namespace
    remap_block_args!(for_body, arg_remap)
    step = remap_value(step, arg_remap)

    return (ForOp(lower, upper, step, iv_arg, for_body, carry_inits), keep_iv ? Int[] : [iv_pos])
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
        push!(new_body, (idx, new_stmt, entry.type, entry.flag))
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
