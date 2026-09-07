# Loop promotion post-pass: LoopOp to WhileOp to ForOp.
#
# The core structurizer produces LoopOps (with ContinueOp/BreakOp). This pass
# recognizes higher-level patterns and promotes them:
#   1. LoopOp with iteration protocol exit to ForOp (direct, via simplify+detect)
#   2. LoopOp with condition-at-top to WhileOp (before/after regions)
#   3. WhileOp with counting pattern to ForOp (lower/upper/step/iv)
#
# Each promotion step remaps block arguments so each region owns its own arg
# namespace (MLIR's region ownership principle).

#=============================================================================
 Top-Level Promotion Pass
=============================================================================#

"""
Enclosing context of the loop being promoted: the enclosing blocks, outermost
first, for SSA lookups, and the enclosing `(IfOp, arm)` pairs, innermost last, for
the entry-guard trace. A range loop can sit inside further conditionals or an outer
loop body within the guarded arm, so the guard is not always the nearest pair;
dominance holds through that nesting.
"""
struct PromoteScope
    blocks::Vector{Block}
    guards::Vector{Tuple{IfOp, Symbol}}
end
PromoteScope() = PromoteScope(Block[], Tuple{IfOp, Symbol}[])

"""Count `BreakOp` terminators reachable inside this loop body, descending into
`IfOp` arms but not into nested loops (whose breaks are their own). A counted or
condition loop has exactly one, its iteration-exit break. A second one is a
secondary dynamic exit (an early `break`/`return` reached mid-body) that `ForOp`
and `WhileOp` cannot represent, since their iteration is fixed, so such a loop must
stay a `LoopOp`. Promoting it would build a `ForOp` body with a stray `BreakOp`
whose exit placeholder leaks at unstructurize, a crash this guard prevents."""
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
where the pattern matches. `scope` carries the enclosing blocks and `(IfOp, arm)`
pairs down the walk (see `PromoteScope`); the legality proofs read them.
"""
function promote_loops!(block::Block, ctx::StructurizeCtx,
                        scope::PromoteScope=PromoteScope())
    push!(scope.blocks, block)
    new_body = SSAMap()
    # Track ForOp promotions: loop_ssa_idx => (removed_positions, ForOp, carry_redirect)
    for_promotions = Dict{Int, Tuple{Vector{Int}, ForOp, Dict{Int,Int}}}()

    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa LoopOp && count_breaks(stmt.body) > 1
            # Secondary dynamic exit (e.g. an early break/return alongside the
            # iteration-exit break): only the general LoopOp can represent it.
            promote_loops!(stmt.body, ctx, scope)
            push!(new_body, (idx, stmt, entry.type, entry.flag))
        elseif stmt isa LoopOp
            # Promote inner loops first.
            promote_loops!(stmt.body, ctx, scope)
            # Try direct LoopOp to ForOp (iteration protocol patterns).
            result, removed, redirect = try_promote_for_from_loop(stmt, idx, block, new_body, ctx, scope)
            if result isa ForOp
                for_promotions[idx] = (removed, result, redirect)
                carry_types = Any[t for (i, t) in enumerate(entry.type.parameters) if i ∉ removed]
                push!(new_body, (idx, result, Tuple{carry_types...}, entry.flag))
            else
                # Fall back to LoopOp to WhileOp to ForOp.
                promoted = try_promote_while(stmt, ctx)
                if promoted !== nothing
                    result2, removed2 = try_promote_for(promoted, idx, block, new_body, ctx, scope)
                    if result2 isa ForOp
                        if isempty(removed2)
                            # The escaping IV is kept as an ordinary carry, so arity
                            # and order are unchanged and post-loop getfields read it
                            # directly: no for_promotions entry, no getfield rewrite.
                            # Carried-value semantics give the empty-loop case its
                            # init, the value we want there.
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
            # Fix getfield for ForOp: removed positions to the bound or a redirect,
            # others to adjusted index.
            loop_ssa = stmt.args[2].id
            field_idx = stmt.args[3]::Int
            removed, for_op, redirect = for_promotions[loop_ssa]
            if field_idx ∈ removed
                target_pos = get(redirect, field_idx, 0)
                if target_pos > 0
                    # Duplicate carry: redirect to surviving carry's adjusted index.
                    adjusted = target_pos - count(p -> p < target_pos, removed)
                    new_gf = Expr(:call, Core.getfield, SSAValue(loop_ssa), adjusted)
                    push!(new_body, (idx, new_gf, entry.type, entry.flag))
                else
                    # `upper` alias for a removed IV/shadow position. Every escaping
                    # removed position is kept as a real carry instead, so this branch
                    # is only reachable for a provably-dead getfield (the IV-escape
                    # check returned false) and the alias is never observed.
                    @assert !_ssa_used_in_block(SSAValue(idx), idx, block) "escaping removed position aliased to upper"
                    push!(new_body, (idx, for_op.upper, entry.type, entry.flag))
                end
            else
                adjusted = field_idx - count(p -> p < field_idx, removed)
                new_gf = Expr(:call, Core.getfield, SSAValue(loop_ssa), adjusted)
                push!(new_body, (idx, new_gf, entry.type, entry.flag))
            end
        elseif stmt isa IfOp
            # Record the arm each nested loop sits in: the entry-guard trace looks
            # for a loop's dominating guard among these.
            push!(scope.guards, (stmt, :then))
            promote_loops!(stmt.then_region, ctx, scope)
            pop!(scope.guards)
            push!(scope.guards, (stmt, :else))
            promote_loops!(stmt.else_region, ctx, scope)
            pop!(scope.guards)
            push!(new_body, (idx, stmt, entry.type, entry.flag))
        elseif stmt isa ControlFlowOp
            for b in blocks(stmt)
                promote_loops!(b, ctx, scope)
            end
            push!(new_body, (idx, stmt, entry.type, entry.flag))
        else
            push!(new_body, (idx, stmt, entry.type, entry.flag))
        end
    end
    block.body = new_body
    pop!(scope.blocks)
end

#=============================================================================
 Counted-Loop Legality
=============================================================================#
#
# A ForOp is built only once the source loop is proved to satisfy the counted-range
# contract (see the `ForOp` docstring): one supported integer type for the IV, bounds
# and step; a predicate whose signedness matches that type; a positive constant
# step; and, per route, ordered entry, endpoint reachability, or a representable
# final update. The prover is bounded to constants (literals and `Core.Const` SSA
# types, checked in overflow-safe `BigInt` arithmetic) and to the one dominating
# entry-guard trace of Julia's unit-range `iterate`. Unknown facts fail the proof
# and the loop keeps its general form; no fact framework, and no function name or
# range type is taken as a contract.

"""The scope of a loop's own regions: its enclosing scope plus `regions`."""
inner_scope(scope::PromoteScope, regions::Block...) =
    PromoteScope(vcat(scope.blocks, collect(regions)), scope.guards)

"""The statement entry defining `v`, searching the scope innermost first."""
function scope_entry(scope::PromoteScope, v::SSAValue)
    for i in length(scope.blocks):-1:1
        entry = get(scope.blocks[i].body, v.id, nothing)
        entry === nothing || return entry
    end
    return nothing
end

"""The lattice type of `v` as seen from the scope (statement entries keep their
inferred type, so a `Core.Const` is visible), or `nothing` when unknown."""
function scope_argextype(ctx::StructurizeCtx, scope::PromoteScope, @nospecialize(v))
    if v isa SSAValue
        entry = scope_entry(scope, v)
        return entry === nothing ? nothing : entry.type
    elseif v isa BlockArgument || v isa Undef
        return v.type
    elseif v isa Argument
        argtypes = (ctx.m::MCFG).argtypes
        return 1 <= v.n <= length(argtypes) ? argtypes[v.n] : nothing
    elseif v isa QuoteNode
        return CC.Const(v.value)
    elseif v isa GlobalRef || v isa SlotNumber || v isa Core.MethodInstance ||
           v isa Core.CodeInstance
        return nothing
    else
        return CC.Const(v)   # literal
    end
end

"""The widened type of `v`, or `nothing`."""
function scope_value_type(ctx::StructurizeCtx, scope::PromoteScope, @nospecialize(v))
    t = scope_argextype(ctx, scope, v)
    return t === nothing ? nothing : widenconst(t)
end

"""The constant value of `v` as `Some(x)`: a literal, a `QuoteNode`, or an SSA
value whose inferred type is a `Core.Const`. `nothing` when not constant."""
function scope_const(ctx::StructurizeCtx, scope::PromoteScope, @nospecialize(v))
    t = scope_argextype(ctx, scope, v)
    return t isa CC.Const ? Some(t.val) : nothing
end

"""Resolve a callee reference (`GlobalRef` or value) to its value, or `nothing`."""
function callee_value(@nospecialize(f))
    if f isa GlobalRef
        isconst(f.mod, f.name) || return nothing
        return getglobal(f.mod, f.name)
    end
    return f
end

"""`(object, field)` of a `getfield(object, field)` call with a constant field
(`Int` position or `Symbol` name), else `nothing`."""
function getfield_operands(@nospecialize(stmt))
    stmt isa Expr && stmt.head === :call && length(stmt.args) == 3 || return nothing
    callee_value(stmt.args[1]) === Core.getfield || return nothing
    f = stmt.args[3]
    f isa QuoteNode && (f = f.value)
    f isa Union{Int, Symbol} || return nothing
    return (stmt.args[2], f)
end

"""
Whether `a` and `b` are the same value: the same SSA value, block argument,
argument or constant, or two `getfield` projections of the same constant field
of the same immutable object. The latter matters for opaque ranges: Julia's
`iterate` reads `r.start`/`r.stop` afresh for the guard, the initial state and
the exit test without necessarily combining the reads. Fields of mutable objects are not
followed: a body may write them between two reads.
"""
function same_value(ctx::StructurizeCtx, scope::PromoteScope, @nospecialize(a), @nospecialize(b))
    a === b && return true
    if a isa SSAValue && b isa SSAValue
        a.id == b.id && return true
        ea = scope_entry(scope, a)
        eb = scope_entry(scope, b)
        (ea === nothing || eb === nothing) && return false
        fa = getfield_operands(ea.stmt)
        fb = getfield_operands(eb.stmt)
        (fa === nothing || fb === nothing) && return false
        fa[2] === fb[2] || return false
        same_value(ctx, scope, fa[1], fb[1]) || return false
        T = scope_value_type(ctx, scope, fa[1])
        return T isa DataType && isconcretetype(T) && !ismutabletype(T)
    elseif a isa BlockArgument && b isa BlockArgument
        return a.id == b.id
    elseif a isa Argument && b isa Argument
        return a.n == b.n
    end
    return false
end

"""Follow a chain of `not_int` calls: `(base value, inverted)`."""
function strip_not(scope::PromoteScope, @nospecialize(v))
    inverted = false
    while v isa SSAValue
        entry = scope_entry(scope, v)
        entry === nothing && break
        stmt = entry.stmt
        (stmt isa Expr && stmt.head === :call && length(stmt.args) == 2 &&
         callee_value(stmt.args[1]) === Core.Intrinsics.not_int) || break
        v = stmt.args[2]
        inverted = !inverted
    end
    return v, inverted
end

"""The step as a positive constant of the IV type `T`, else `nothing`."""
function positive_const_step(ctx::StructurizeCtx, scope::PromoteScope, @nospecialize(step), T::DataType)
    c = scope_const(ctx, scope, step)
    c === nothing && return nothing
    st = something(c)
    return st isa T && st > zero(T) ? st : nothing
end

"""The value of `v` if it is a constant of type `T`, else `nothing`."""
function typed_const(ctx::StructurizeCtx, scope::PromoteScope, @nospecialize(v), T::DataType)
    c = scope_const(ctx, scope, v)
    c === nothing && return nothing
    x = something(c)
    return x isa T ? x : nothing
end

"""
Prove that a unit-range loop is entered only when `lower <= upper`, from Julia's
inlined `iterate(::AbstractUnitRange)` guard (1.11 and 1.12 lower it alike):

    g = if slt_int(upper, first)       # ult_int for an unsigned IV
          yield true, undef, ...
        else
          yield false, first, ...
        end
    if not_int(getfield(g, flag_position))
        loop init(iv = getfield(g, initial_iv_position), ...)
    end

`lower` must be a projection of `g`; the loop must sit, possibly through further
nesting, in an arm of an enclosing `IfOp` whose condition is the flag projection
of the same `g`, taken when the flag is false (either polarity, followed through
`not_int`); the two flags must be the distinct `Bool` constants; the flag-false
arm must yield `first`, the very value the guard compared `upper` against, at the
projected position; and that comparison must have been false on that arm. Value
identity follows `same_value`, so `upper` may be a fresh read of the same
immutable range field. Anything else fails: no other entry guard is trusted.
"""
function unit_range_entry_proof(ctx::StructurizeCtx, scope::PromoteScope,
                                @nospecialize(lower), @nospecialize(upper), T::DataType)
    lower isa SSAValue || return false
    lentry = scope_entry(scope, lower)
    lentry === nothing && return false
    proj = getfield_operands(lentry.stmt)
    proj === nothing && return false
    g_val, iv_pos = proj
    (g_val isa SSAValue && iv_pos isa Int) || return false
    gentry = scope_entry(scope, g_val)
    gentry === nothing && return false
    g = gentry.stmt
    g isa IfOp || return false
    then_y = g.then_region.terminator
    else_y = g.else_region.terminator
    (then_y isa YieldOp && else_y isa YieldOp) || return false

    for (gif, arm) in Iterators.reverse(scope.guards)
        cond, inverted = strip_not(scope, gif.condition)
        cond isa SSAValue || continue
        centry = scope_entry(scope, cond)
        centry === nothing && continue
        fproj = getfield_operands(centry.stmt)
        fproj === nothing && continue
        (fproj[1] isa SSAValue && fproj[1].id == g_val.id && fproj[2] isa Int) || continue
        flag_pos = fproj[2]
        (flag_pos <= length(then_y.values) && flag_pos <= length(else_y.values)) || continue
        then_flag = then_y.values[flag_pos]
        else_flag = else_y.values[flag_pos]
        (then_flag isa Bool && else_flag isa Bool && then_flag != else_flag) || continue
        # The loop's arm is taken when `gif.condition` is true (:then) or false
        # (:else); undo the inversions to get the flag on that path. Only the
        # "not done" path (flag false) proves entry.
        ((arm === :then) ⊻ inverted) && continue

        entered_then = !then_flag
        yields = entered_then ? then_y : else_y
        iv_pos <= length(yields.values) || return false
        first = yields.values[iv_pos]
        # `first` may be defined inside the entered arm (a fresh `r.start` read).
        arm_scope = inner_scope(scope, entered_then ? g.then_region : g.else_region)

        # g's condition is the range-order test; it was false on the entered arm.
        gcond, ginv = strip_not(scope, g.condition)
        gcond isa SSAValue || return false
        gc = scope_entry(scope, gcond)
        gc === nothing && return false
        cmp = gc.stmt
        (cmp isa Expr && cmp.head === :call && length(cmp.args) == 3) || return false
        want = forop_iv_signed(T) ? Core.Intrinsics.slt_int : Core.Intrinsics.ult_int
        callee_value(cmp.args[1]) === want || return false
        (entered_then ⊻ ginv) && return false   # `upper < first` held: no entry proof
        u, f = cmp.args[2], cmp.args[3]
        same_value(ctx, scope, u, upper) || return false
        same_value(ctx, arm_scope, f, first) || return false
        (scope_value_type(ctx, scope, u) === T && scope_value_type(ctx, scope, f) === T) ||
            return false
        return true
    end
    return false
end

"""
Legality of the iterate-protocol route: a `LoopOp` whose exit is `iv === bound`
before the increment `iv + step`, as an inclusive `ForOp(lower, bound, step)`.
Requires the shared type/step facts, and either constant ordered endpoints with
`bound` on the step grid, or (unit step) the dominating unit-range entry guard.
Returns the IV type, or `nothing` when the contract is not established.
"""
function counted_loop_legal_iterate(ctx::StructurizeCtx, scope::PromoteScope,
                                    iv_arg::BlockArgument, @nospecialize(lower),
                                    @nospecialize(bound), @nospecialize(step))
    T = forop_iv_type(iv_arg.type)
    T === nothing && return nothing
    scope_value_type(ctx, scope, lower) === T || return nothing
    scope_value_type(ctx, scope, bound) === T || return nothing
    st = positive_const_step(ctx, scope, step, T)
    st === nothing && return nothing
    lo = typed_const(ctx, scope, lower, T)
    up = typed_const(ctx, scope, bound, T)
    if lo !== nothing && up !== nothing
        # Constant endpoints: the loop is entered unconditionally, so it visits
        # `lower` and must reach `bound` without wrapping.
        lo <= up || return nothing
        (big(up) - big(lo)) % big(st) == 0 || return nothing
        return T
    end
    # A larger step needs the alignment fact, which only constants supply here.
    st == one(T) || return nothing
    unit_range_entry_proof(ctx, scope, lower, bound, T) || return nothing
    return T
end

"""
Legality of the header-tested route: a `WhileOp` testing `iv < bound` (`is_le`
false) or `iv <= bound` (`is_le` true) with the compare `func`, updating
`iv + step`, as an exclusive or inclusive `ForOp`. Beyond the shared type/step
facts and the predicate's signedness matching the IV type:

- `<`: the first update reaching or crossing `bound` must be representable. Unit
  step needs nothing more; a larger step needs a constant `bound` with
  `bound + step - 1 <= typemax`, or constant endpoints whose exact final update
  fits.
- `<=`: the source update and the following failed test must amount to stopping
  at `bound`. Unit step needs a constant `bound < typemax`; a larger step needs
  constant endpoints proving alignment and a representable `bound + step`.

Returns the IV type, or `nothing`; the `WhileOp` then keeps its own semantics,
wraparound included.
"""
function counted_loop_legal_while(ctx::StructurizeCtx, scope::PromoteScope,
                                  iv_arg::BlockArgument, @nospecialize(lower),
                                  @nospecialize(bound), @nospecialize(step),
                                  is_le::Bool, @nospecialize(func))
    T = forop_iv_type(iv_arg.type)
    T === nothing && return nothing
    want = if forop_iv_signed(T)
        is_le ? Core.Intrinsics.sle_int : Core.Intrinsics.slt_int
    else
        is_le ? Core.Intrinsics.ule_int : Core.Intrinsics.ult_int
    end
    callee_value(func) === want || return nothing
    scope_value_type(ctx, scope, lower) === T || return nothing
    scope_value_type(ctx, scope, bound) === T || return nothing
    st = positive_const_step(ctx, scope, step, T)
    st === nothing && return nothing
    lo = typed_const(ctx, scope, lower, T)
    up = typed_const(ctx, scope, bound, T)
    tmax = big(typemax(T))
    if !is_le
        st == one(T) && return T          # `iv < bound` makes `iv + 1 <= bound`
        up === nothing && return nothing
        big(up) + big(st) - 1 <= tmax && return T
        lo === nothing && return nothing
        lo >= up && return T              # statically empty: no update runs
        last = big(lo) + div(big(up) - 1 - big(lo), big(st)) * big(st)
        return last + big(st) <= tmax ? T : nothing
    end
    if st == one(T)
        up === nothing && return nothing
        return big(up) < tmax ? T : nothing   # `bound + 1` fits and fails the test
    end
    (lo === nothing || up === nothing) && return nothing
    lo > up && return T                       # statically empty
    (big(up) - big(lo)) % big(st) == 0 || return nothing   # lands on the bound
    return big(up) + big(st) <= tmax ? T : nothing        # final update fits, exits
end

#=============================================================================
 Hoisting Loop-Defined Bounds and Steps
=============================================================================#

# Hoisting may execute a statement on a path that previously skipped it. Require
# no side effects, exceptions or undefined behavior, and a consistent result.
# Termination is checked separately for compatibility with Julia 1.11.
const IR_FLAGS_HOISTABLE = CC.IR_FLAGS_REMOVABLE | CC.IR_FLAG_CONSISTENT | CC.IR_FLAG_NOUB

"""Whether a statement is known to terminate, including when speculated."""
function terminates(entry)
    entry.flag & CC.IR_FLAG_TERMINATES != 0 && return true
    # Julia 1.11 never sets the termination bit. Recognize only builtins with
    # bounded execution; llvmcall and atomic_pointermodify can run user code.
    VERSION >= v"1.12-" && return false
    stmt = entry.stmt
    stmt isa Expr && stmt.head === :call || return false
    f = stmt.args[1]
    if f isa GlobalRef
        isconst(f.mod, f.name) || return false
        f = getglobal(f.mod, f.name)
    end
    return f === Core.getfield || f === Core.tuple ||
           (f isa Core.IntrinsicFunction && f !== Core.Intrinsics.llvmcall &&
            f !== Core.Intrinsics.atomic_pointermodify)
end

"""Whether `entry` can move ahead of the loop. Operands must be defined outside
its block arguments and regions; transitive hoisting is not attempted."""
function hoistable_loop_def(entry, args::Vector{BlockArgument}, regions::Block...)
    entry.flag & IR_FLAGS_HOISTABLE == IR_FLAGS_HOISTABLE || return false
    terminates(entry) || return false
    stmt = entry.stmt
    stmt isa Expr || return false
    for a in stmt.args
        if a isa BlockArgument
            any(arg -> arg.id == a.id, args) && return false
        elseif a isa SSAValue
            any(r -> haskey(r.body, a.id), regions) && return false
        end
    end
    return true
end

"""Whether deleting a statement preserves effects and termination."""
function droppable_loop_def(entry)
    entry.flag & CC.IR_FLAGS_REMOVABLE == CC.IR_FLAGS_REMOVABLE || return false
    return terminates(entry)
end

"""Collect loop-invariant bound/step definitions to move before a `ForOp`.
Return `nothing` if either value depends on the loop. Preserve SSA ids so uses
remaining inside the loop resolve to the relocated definitions."""
function collect_hoists(vals, args::Vector{BlockArgument}, regions::Block...)
    hoisted = SSAMap()
    for v in vals
        if v isa BlockArgument
            any(a -> a.id == v.id, args) && return nothing
        elseif v isa SSAValue && !haskey(hoisted, v.id)
            for r in regions
                entry = get(r.body, v.id, nothing)
                entry === nothing && continue
                hoistable_loop_def(entry, args, regions...) || return nothing
                push!(hoisted, (v.id, entry.stmt, entry.type, entry.flag))
                break
            end
        end
    end
    return hoisted
end

#=============================================================================
 LoopOp to ForOp (direct, for iteration protocol patterns)
=============================================================================#

"""
Simplify a LoopOp body that has the iteration protocol exit pattern:
  inner_if(cond), done-flag, getfields, not_int, outer_if(continue/break)
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
            if callee_value(func) === Core.Intrinsics.not_int
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

    # inner_result should be an IfOp in the body.
    inner_entry = get(body.body, inner_result.id, nothing)
    inner_entry === nothing && return nothing
    inner = inner_entry.stmt
    inner isa IfOp || return nothing

    # Verify inner yield[flag_pos] is a boolean constant in both branches.
    inner.then_region.terminator isa YieldOp || return nothing
    inner.else_region.terminator isa YieldOp || return nothing
    then_yield = inner.then_region.terminator::YieldOp
    else_yield = inner.else_region.terminator::YieldOp
    flag_pos <= length(then_yield.values) && flag_pos <= length(else_yield.values) || return nothing
    then_flag = then_yield.values[flag_pos]
    else_flag = else_yield.values[flag_pos]
    (then_flag isa Bool && else_flag isa Bool && then_flag != else_flag) || return nothing

    # Determine which inner branch is "done" (flag=true) and which is "not done".
    done_yield = then_flag ? then_yield : else_yield
    cont_yield = then_flag ? else_yield : then_yield
    done_body_region = then_flag ? inner.then_region : inner.else_region
    cont_body_region = then_flag ? inner.else_region : inner.then_region

    # Determine which outer branch is "continue" and which is "break".
    # inverted=false: outer condition = flag, so true=done means break.
    # inverted=true:  outer condition = not_int(flag), so true=not_done means continue.
    if inverted
        cont_term = then_t
        break_term = else_t
    else
        break_term = then_t
        cont_term = else_t
    end
    cont_term isa ContinueOp || return nothing

    # Only the protocol projections and flag inversion disappear between the
    # inner decision and the outer dispatch. Other work, including work in the
    # dispatch arms, must remain in the general loop.
    isempty(outer.then_region.body) && isempty(outer.else_region.body) || return nothing
    past_inner = false
    for (sidx, sentry) in body.body
        sidx == inner_result.id && (past_inner = true; continue)
        past_inner || continue
        sidx == outer_idx && break
        s = sentry.stmt
        projection = getfield_operands(s)
        if projection !== nothing && projection[1] === inner_result
            continue
        end
        if sidx == outer.condition.id && inverted
            continue  # the not_int already matched above
        end
        return nothing
    end

    # Build getfield-to-inner_yield substitution maps.
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

    # Preserve which value of the inner condition selects the done arm.
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

    merged_if = then_flag ? IfOp(inner.condition, merged_then, merged_else) :
                            IfOp(inner.condition, merged_else, merged_then)

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

"""Check whether a loop result field has a live use. An escaping IV or shadow
must remain a carry: the bound need not equal its final value (e.g. an empty
while loop, or the post-increment IV of a `<=` loop)."""
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

"""Check for uses after `after_idx` or in the terminator, including nested regions."""
function _ssa_used_in_block(ssa::SSAValue, after_idx::Int, block::Block)
    past = false
    for (sidx, sentry) in block.body
        if sidx == after_idx
            past = true
            continue
        end
        past || continue
        _refs_ssa_deep(sentry.stmt, ssa) && return true
    end
    block.terminator !== nothing && _refs_ssa_deep(block.terminator, ssa) && return true
    return false
end

function _refs_ssa(@nospecialize(val), ssa::SSAValue)
    val === ssa && return true
    if val isa Expr
        return any(a -> _refs_ssa(a, ssa), val.args)
    elseif val isa PiNode
        return _refs_ssa(val.val, ssa)
    elseif val isa ConditionOp
        return _refs_ssa(val.condition, ssa) || any(v -> v === ssa, val.args)
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

"""Deep `_refs_ssa` that also recurses into nested control-flow regions and a
`Block`, so a use buried in a nested IfOp or loop body still counts."""
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
                                    new_body::SSAMap, ctx::StructurizeCtx,
                                    scope::PromoteScope)
    # Simplify the exit structure (returns a new Block, original is untouched).
    body = simplify_loop_exit(loop.body)
    body === nothing && return (loop, Int[], Dict{Int,Int}())

    # After simplification the body should end with IfOp(cond, break, continue)
    # or vice versa.
    isempty(body.body) && return (loop, Int[], Dict{Int,Int}())
    last_stmt = body.body.stmts[end]
    last_stmt isa IfOp || return (loop, Int[], Dict{Int,Int}())
    if_op = last_stmt

    then_t = if_op.then_region.terminator
    else_t = if_op.else_region.terminator

    # Determine break/continue branches (either polarity).
    if then_t isa BreakOp && else_t isa ContinueOp
        break_op, continue_op = then_t, else_t
        cont_region = if_op.else_region
    elseif then_t isa ContinueOp && else_t isa BreakOp
        continue_op, break_op = then_t, else_t
        cont_region = if_op.then_region
    else
        return (loop, Int[], Dict{Int,Int}())
    end

    # Promotion drops the exit arm and executes the continuation arm on the
    # final iteration too. Check the exit arm here; continuation speculation is
    # checked below, once the integer recurrence has been identified.
    exit_region = then_t isa BreakOp ? if_op.then_region : if_op.else_region
    all(droppable_loop_def(e) for (_, e) in exit_region.body) ||
        return (loop, Int[], Dict{Int,Int}())

    # The exit condition must compare the IV with the bound.
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
    # slt_int/sle_int patterns are handled by the WhileOp-to-ForOp path.
    is_eq = callee_value(func) === Core.:(===)
    (is_eq && then_t isa BreakOp) || return (loop, Int[], Dict{Int,Int}())

    iv_candidate isa BlockArgument || return (loop, Int[], Dict{Int,Int}())
    iv_pos = findfirst(a -> a.id == iv_candidate.id, body.args)
    iv_pos === nothing && return (loop, Int[], Dict{Int,Int}())

    # Find step: add_int(iv_arg, step) in the continue branch at iv_pos.
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
                if callee_value(sfunc) === Core.Intrinsics.add_int &&
                   s.args[2] isa BlockArgument && s.args[2].id == iv_candidate.id
                    step = s.args[3]
                    step_ssa = step_val.id
                end
            end
        end
    end
    step === nothing && return (loop, Int[], Dict{Int,Int}())

    # The counted-range contract must be proved before anything is committed (see
    # `counted_loop_legal_iterate`): an equality exit with the protocol shape is
    # not itself a proof that the range is entered in order or reaches its end.
    lower = loop.init_values[iv_pos]
    counted_loop_legal_iterate(ctx, inner_scope(scope, body, cont_region),
                               iv_candidate, lower, bound, step) === nothing &&
        return (loop, Int[], Dict{Int,Int}())

    # The matched integer addition is total, including at the endpoint. Other
    # continuation statements need the compiler's speculation guarantees.
    all(sidx == step_ssa ||
        (e.flag & IR_FLAGS_HOISTABLE == IR_FLAGS_HOISTABLE && terminates(e))
        for (sidx, e) in cont_region.body) || return (loop, Int[], Dict{Int,Int}())

    # Step and bound must be loop-invariant: not a block argument of the loop, and
    # not defined in the body (the bound is computed in the header part of `body`,
    # the step in the continue branch) unless that definition can be relocated ahead
    # of the loop; see `collect_hoists`.
    hoisted = collect_hoists((bound, step), body.args, body, cont_region)
    hoisted === nothing && return (loop, Int[], Dict{Int,Int}())

    # Shadow IV detection: other args whose continue value is the same SSA as
    # the IV's continue value (they track the same induction variable).
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
    carry_redirect = Dict{Int, Int}()  # removed_pos => surviving_pos
    seen_continues = Dict{Any, Int}()  # continue_value => first non-removed pos
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
    # Pre-scan parent block once to map getfield positions to SSA indices.
    gf_ssa_for_pos = Dict{Int, Int}()  # loop result position => getfield SSA idx
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

    # Partition `removed` by whether each position escapes. A removed position (the
    # IV or one of its shadows) would otherwise be aliased to `upper` post-loop, which
    # is wrong for an empty loop whose final IV is the init. So any escaping position
    # becomes a real kept carry (read back normally) and the rest stay removed (their
    # `upper` alias is then provably dead). A duplicate-carry redirect stays removed;
    # an Undef-init dup is folded into its survivor, not a value that escapes on its own.
    kept = Int[]
    for r in removed
        haskey(carry_redirect, r) && continue
        loop_result_pos_escapes(idx, r, parent_block) && push!(kept, r)
    end
    # Drop kept positions from `removed` before any index adjustment below reads it.
    removed = setdiff(removed, kept)

    # Build ForOp.
    # Loop-defined bound/step definitions move ahead of the loop that reads them.
    for (hidx, hentry) in hoisted
        push!(new_body, (hidx, hentry.stmt, hentry.type, hentry.flag))
    end
    # The `===` exit visits `bound` itself and stops there, which is exactly the
    # inclusive ForOp, with `bound` taken verbatim as the upper limit. An exclusive
    # `bound + step` would wrap for a range ending at `typemax` of its type (or any
    # narrow integer type) and lose the whole loop. The legality proof established
    # that every entry satisfies `lower <= bound` (so the ForOp's own entry guard
    # changes nothing) and that `bound` lies on the step grid.
    upper = bound

    iv_arg = BlockArgument(alloc_arg!(ctx), iv_candidate.type)
    for_body = Block()
    arg_remap = Dict{Int, BlockArgument}()

    # Map (still-)removed IV / shadow IVs to ForOp's iv_arg (skip duplicate carries).
    for r in removed
        haskey(carry_redirect, r) && continue
        arg_remap[body.args[r].id] = iv_arg
    end

    # Retained carries get fresh BlockArguments in original index order, each with
    # its own init. This covers genuine carries and kept escaping IV/shadows (the
    # latter are no longer in `removed`). A kept escaping IV/shadow holds the current
    # IV in-body, e.g. the value an `acc += i` reads, so its in-body uses resolve to
    # `iv_arg` and its fresh for-arg is a write-only carry slot that only exposes the
    # post-loop result. A genuine carry maps its body uses to its own for-arg.
    non_iv_inits = IRValue[]
    for (i, arg) in enumerate(body.args)
        i ∈ removed && continue
        for_arg = BlockArgument(alloc_arg!(ctx), arg.type)
        push!(for_body.args, for_arg)
        arg_remap[arg.id] = (i ∈ kept) ? iv_arg : for_arg
        push!(non_iv_inits, loop.init_values[i])
    end

    # Map duplicate carries to their surviving equivalent's BlockArgument.
    for (dup_pos, surv_pos) in carry_redirect
        arg_remap[body.args[dup_pos].id] = arg_remap[body.args[surv_pos].id]
    end

    # ContinueOp values. A kept escaping position carries `iv_arg` itself, not its
    # lifted continue. The iterate protocol advances the state before re-checking, so
    # the lifted continue is the advanced value `iv+step`, one past the bound.
    # Carrying `iv_arg` makes the kept carry's last value the last in-body IV, the
    # bound itself, matching the LoopOp's break, the pre-advance current value. The
    # empty range is guarded by the outer `if`, so the init is read only when the
    # loop ran.
    cont_values = IRValue[]
    for (i, v) in enumerate(continue_op.values)
        i ∈ removed && continue
        push!(cont_values, i ∈ kept ? iv_arg : v)
    end

    # The IV increment (`step_ssa = iv + step`) is implicit in the range. Kept
    # carries reference `iv_arg`, not the increment, so the statement is needed only
    # if some other retained body stmt or surviving carried value reads it. Keep it
    # only when referenced. A dead increment is harmless; a missing one dangles.
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

    # Body: stmts before the exit IfOp plus continue branch stmts (minus dead increment
    # and the bound/step definitions hoisted above).
    for (sidx, sentry) in body.body
        sidx == last_idx && break
        haskey(hoisted, sidx) && continue
        push!(for_body.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
    end
    for (sidx, sentry) in cont_region.body
        step_ssa !== nothing && sidx == step_ssa && !incr_used && continue  # drop dead IV increment
        haskey(hoisted, sidx) && continue
        push!(for_body.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
    end

    for_body.terminator = ContinueOp(cont_values)

    remap_block_args!(for_body, arg_remap)
    step = remap_value(step, arg_remap)

    return (ForOp(lower, upper, step, iv_arg, for_body, non_iv_inits; inclusive=true),
            removed, carry_redirect)
end

#=============================================================================
 LoopOp to WhileOp
=============================================================================#

"""
Try to promote a LoopOp to WhileOp if the body has the form:
  header_stmts; IfOp(cond, then{...ContinueOp}, else{BreakOp})
"""
function try_promote_while(loop::LoopOp, ctx::StructurizeCtx)
    body = loop.body
    # The body should end with an IfOp (the last stmt).
    isempty(body.body) && return nothing

    last_idx = body.body.ssa_idxes[end]
    last_stmt = body.body.stmts[end]
    last_stmt isa IfOp || return nothing

    if_op = last_stmt

    # Determine which branch continues and which breaks.
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

    # Only promote when cond=true means stay (the standard while pattern).
    # Inverted patterns (cond=true means break) would require condition negation.
    if is_else_continue
        return nothing
    end

    # Standard pattern: cond=true means continue, cond=false means break.
    continue_op = stay_region.terminator::ContinueOp

    # Guard: ContinueOp values must only reference block args or values defined
    # in the stay region. If they reference header SSAs (which go into `before`),
    # the WhileOp's `after` region can't see them, so keep as LoopOp.
    for val in continue_op.values
        if val isa SSAValue && !haskey(stay_region.body, val.id)
            return nothing
        end
    end

    # The sibling before/after regions cannot share header SSA definitions.
    # Keep the LoopOp if the body reads one, including through a nested region.
    for (sidx, _) in body.body
        sidx == last_idx && break
        _refs_ssa_deep(stay_region, SSAValue(sidx)) && return nothing
    end

    # Before region: header stmts (everything before the IfOp).
    before = Block()
    for (sidx, sentry) in body.body
        sidx == last_idx && break
        push!(before.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
    end
    for arg in body.args
        push!(before.args, arg)
    end

    # ConditionOp args = before block args, passed to the after region when cond is true.
    cond_args = IRValue[arg for arg in before.args]
    before.terminator = ConditionOp(cond, cond_args)

    # After region: stay_region body plus YieldOp with carried values (back to before).
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

    # Remap before-region block arg references to after-region block args, so each
    # region references its own args (MLIR's ownership principle).
    remap_block_args!(after, arg_remap)

    return WhileOp(before, after, loop.init_values)
end

#=============================================================================
 WhileOp to ForOp
=============================================================================#

"""
Try to promote a WhileOp to ForOp by detecting counting patterns.
Returns `(promoted_op, removed)` where `removed::Vector{Int}` lists the loop-result
positions the ForOp dropped (the caller adjusts post-loop `getfield`s accordingly):
- `(ForOp, [iv_pos])`: the IV was removed, the usual case, since it is implicit in
  the range.
- `(ForOp, Int[])`: the IV escapes, so it is kept as an ordinary carry. The result
  arity and order match the original WhileOp, and the empty (zero-trip) case reads
  back the init rather than the bound. No position is removed.
- `(op, Int[])` with `op` still a WhileOp: not promoted.
"""
function try_promote_for(op, idx::Int, parent_block::Block, new_body::SSAMap,
                          ctx::StructurizeCtx, scope::PromoteScope)
    op isa WhileOp || return (op, Int[])

    # Look for a condition that is slt_int/sle_int on a block arg vs a loop-invariant bound.
    before = op.before
    before.terminator isa ConditionOp || return (op, Int[])
    cond_op = before.terminator

    # Find the condition expression.
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

    # Check condition function. `===` is not a counting pattern (try_promote_for_from_loop
    # handles it).
    is_slt = func isa GlobalRef && func.name in (:slt_int, :ult_int)
    is_sle = func isa GlobalRef && func.name in (:sle_int, :ule_int)
    (is_slt || is_sle) || return (op, Int[])

    # IV must be a block argument.
    iv_candidate isa BlockArgument || return (op, Int[])

    # Find IV's position in args.
    iv_pos = findfirst(a -> a.id == iv_candidate.id, before.args)
    iv_pos === nothing && return (op, Int[])

    # A ForOp does not carry its IV as a result. If the IV is read after the loop,
    # keep it as an ordinary carry (`keep_iv`) so the post-loop read is a normal
    # result, correct for both the empty (init) and non-empty (last continue = the
    # post-increment IV) cases. If the IV does not escape, drop it; it is redundant
    # with the range.
    keep_iv = loop_result_pos_escapes(idx, iv_pos, parent_block)

    # Find step: look in the after region for add_int(iv_arg, step).
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
                if callee_value(sfunc) === Core.Intrinsics.add_int
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

    # The counted-range contract must be proved before anything is committed (see
    # `counted_loop_legal_while`): the `<`/`<=` shape alone does not rule out a
    # wrapping final update.
    counted_loop_legal_while(ctx, inner_scope(scope, before, after), iv_candidate,
                             op.init_values[iv_pos], bound, step, is_sle, func) === nothing &&
        return (op, Int[])

    # Step and bound must be loop-invariant: not a block argument of either region,
    # and not defined in the loop unless that definition can be relocated ahead of it;
    # see `collect_hoists`. This matters for the bound in particular: the ForOp drops
    # the `before` region wholesale, so a bound computed there (`while i <= r.stop` on
    # an opaque `r`) would otherwise dangle.
    hoisted = collect_hoists((bound, step), vcat(before.args, after.args), before, after)
    hoisted === nothing && return (op, Int[])

    # Promotion replaces the header with a range test. Any remaining header
    # statement must be safe to delete, e.g. `while (f(); i <= n)` must retain f().
    for (sidx, sentry) in before.body
        sidx == cond_val.id && continue
        haskey(hoisted, sidx) && continue
        droppable_loop_def(sentry) || return (op, Int[])
        _refs_ssa_deep(after, SSAValue(sidx)) && return (op, Int[])
    end

    # Build ForOp. The bound is taken verbatim: `<` is the exclusive ForOp's test
    # and `<=` the inclusive one's, so no `bound + 1` is computed (it would wrap
    # for a bound at `typemax`; the proof above covers the source's own update).
    lower = op.init_values[iv_pos]
    upper = bound

    # Loop-defined bound/step definitions move ahead of the loop that reads them.
    for (hidx, hentry) in hoisted
        push!(new_body, (hidx, hentry.stmt, hentry.type, hentry.flag))
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

    # Build ForOp body: copy the after region, remove the IV increment, remap args.
    for_body = Block()
    arg_remap = Dict{Int, BlockArgument}()

    for (i, arg) in enumerate(after.args)
        (i == iv_pos && !keep_iv) && continue
        for_arg = BlockArgument(alloc_arg!(ctx), arg.type)
        push!(for_body.args, for_arg)
        arg_remap[arg.id] = for_arg
        # Also map the corresponding before arg.
        if i <= length(before.args)
            arg_remap[before.args[i].id] = for_arg
        end
    end

    # In-body IV references always resolve to the implicit induction variable
    # (`iv_arg`), overriding the write-only carry slot the kept-IV loop just mapped
    # above: the kept carry is computed (continue = the increment) but never read.
    arg_remap[after_iv_arg.id] = iv_arg
    arg_remap[before_iv_arg.id] = iv_arg

    # The IV increment (`carried_val = iv + step`) is implicit in a ForOp, so it is
    # normally dropped. It must stay when something else reads it: another body
    # statement (e.g. `s += k` where `k` is the post-increment IV), or the kept-IV
    # carry whose continue is the increment. When kept it is remapped below to read
    # the ForOp's induction variable; dropping it in that case leaves a dangling SSA
    # reference (`%k used but not defined`).
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
        haskey(hoisted, sidx) && continue  # relocated ahead of the loop
        push!(for_body.body, (sidx, sentry.stmt, sentry.type, sentry.flag))
    end

    # ContinueOp carried values. At `iv_pos` (when kept) this is `carried_val`, the
    # increment SSA = `iv + step`; its last value is the post-increment IV (`upper`
    # for `<`, `upper + 1` for `<=`), so the kept carry's result matches
    # `while`-counted semantics.
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

    return (ForOp(lower, upper, step, iv_arg, for_body, carry_inits; inclusive=is_sle),
            keep_iv ? Int[] : [iv_pos])
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
