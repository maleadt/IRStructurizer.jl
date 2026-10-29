#=============================================================================
 JuliaLowering.jl's try/catch shapes as round-trip tests, lifted with
 `exceptions=:structured`.

 Like test/julialowering_cases.jl, whose helpers (`jl_f`, `jl_log`, ...) these
 cases use, with the round-trip harness of test/setup.jl. They cover every
 try/catch/else/finally combination in tail, value and statement position, returns
 out of nested trys and catches, `@goto` out of trys and catches, and trys in loops,
 comprehensions and closures. Cases marked `(added)`: irreducible loops built from
 `@goto` with trys inside, around and entering them, returns from catches two and
 three deep, finally with every exit kind, ScopedValues, and bodies that never
 complete.

 `jl_eh_check` checks the structured IR (at least one `EnterNode` in the input, one
 `TryOp` per `EnterNode`, and no `EnterNode`, `:leave` or `PhiCNode` left), then
 round-trips it as `jl_check` does, including the exception-stack depth after each
 call. Every case runs with and without loop promotion, with `Any` arguments, and
 with the optimizer stopped after its first and second compaction.
=============================================================================#

"""Lift `f` with `exceptions=:structured`, check the structured IR, and round-trip it
(`rt_compare`). The input IR must hold at least `min_enters` `EnterNode`s. Returns the
problems found."""
function jl_eh_check(f, inputs; promote=true, argtypes=Tuple{map(typeof, first(inputs))...},
                     optimize_until=nothing, min_enters=1)
    ir, _ = only(code_ircode(f, argtypes; optimize_until))
    nenter = count(s -> s isa Core.EnterNode, ir.stmts.stmt)
    sci = StructuredIRCode(ir; exceptions=:structured, promote)
    problems = String[]
    ntry = 0
    for b in IRStructurizer.eachblock(sci), (_, e) in b.body
        s = e.stmt
        s isa IRStructurizer.TryOp && (ntry += 1)
        if s isa Core.EnterNode || s isa Core.PhiCNode || (s isa Expr && s.head === :leave)
            push!(problems, "leftover $(typeof(s)) in the structured IR")
        end
    end
    nenter >= min_enters ||
        push!(problems, "$nenter EnterNodes, expected at least $min_enters: the try/catch is gone")
    ntry == nenter || push!(problems, "$ntry TryOps for $nenter EnterNodes")
    append!(problems, rt_compare(JL_LOG, f, rt_lower(sci), inputs))
    return problems
end

#=============================================================================
 try / catch / else / finally
=============================================================================#

# exceptions.jl "tail position"
jl_try_tail(x) = try jl_f(x) catch; 2 end
function jl_try_error_tail(x)
    try
        x > 0 && jl_error("hi")
        1
    catch
        2
    end
end
jl_try_catch_exc(x) = try x > 0 ? jl_error("hi") : x catch exc; exc end
jl_try_else_tail(x) = try jl_f(x) catch; 2 else 3 end
function jl_try_return_then_return(x)     # `try return 1 catch end; return 2`
    try
        return jl_f(x)
    catch
    end
    return 2
end
function jl_try_return_fallthrough(x)     # `try return 1 catch end` (nothing on catch)
    try
        return jl_f(x)
    catch
    end
end
function jl_while_catch_break(n)          # `while true; try error() catch; x = 2; break end end`
    x = -1
    i = n
    while true
        try
            i = jl_f(i)
        catch
            x = 2
            break
        end
    end
    (x, i)
end
function jl_while_try_break(n)            # `while true; try x = 2; break catch end end`
    x = -1
    while true
        try
            x = jl_f(n)
            break
        catch
            n -= 5
        end
    end
    x
end

# exceptions.jl "value position"
function jl_try_value_exc(x)
    y = try
        x > 0 && jl_error("hi")
        x
    catch exc
        exc
    end
    y
end
function jl_try_value_else(x)
    y = try
        jl_f(x)
    catch
        2
    else
        3
    end
    y
end

# exceptions.jl "not value/tail position"
function jl_try_assign(x)
    y = -1
    try
        jl_f(x)
        y = 1
    catch
        y = 2
    end
    y
end
function jl_try_assign_exc(x)
    y = -1
    try
        y = x > 0 ? jl_error("hi") : x
    catch exc
        y = exc
    end
    y
end
function jl_try_assign_else(x)
    y = -1
    try
        jl_f(x)
        y = 1
    catch
        y = 2
    else
        y = 3
    end
    y
end

# exceptions.jl "exception stack": the outer catch sees both exceptions.
function jl_exception_stack(x)
    try
        try
            jl_f(x)
        catch
            jl_error("ho")
        end
    catch
        a = []
        for e in current_exceptions()
            push!(a, e.exception)
        end
        a
    end
end
# (added) every exit from a catch pops the exception stack again.
function jl_exception_stack_balanced(x)
    try
        jl_f(x)
    catch
    end
    for i in 1:2
        try
            jl_g(x - 15)
        catch
            continue
        end
    end
    length(current_exceptions())
end

# exceptions.jl "try/finally"
function jl_finally_assign(x)
    y = -1
    try
        y = jl_f(x)
    finally
        jl_log(y)
        y = 2
    end
    y
end
function jl_try_finally_in_try(x)
    y = -1
    try
        try
            jl_f(x)
            y = 1
        finally
            y = 2
        end
    catch
    end
    y
end
function jl_nested_finally(x::Bool, c::Int)     # `nested_finally(a, x, b, c)`
    try
        try
            if x
                return jl_f(c)
            end
            c
        finally
            jl_log(1)
        end
    finally
        jl_log(2)
    end
end
jl_try_catch_finally(x) = try jl_f(x) catch; 2 finally jl_log(3) end

# compat.jl "semantics only"
function jl_catch_else_finally(x)       # `try; 1; catch e; e; else; 2; finally; 3; end`
    try
        jl_f(x)
    catch e
        e
    else
        jl_log(:else)
        2
    finally
        jl_log(:finally)
    end
end
jl_throw_catch(x) = try x > 0 && jl_throw(x); 0 catch e; e end          # `try throw(0) catch e; 1 end`
jl_try_finally_value(x) = try jl_f(x) finally jl_log(1) end           # `try 0 finally 1 end`
function jl_throw_catch_finally(x)      # `try throw(0) catch e; 1 finally 2 end`
    try
        x > 0 && jl_throw(x)
        0
    catch e
        e + 1
    finally
        jl_log(2)
    end
end
function jl_throw_catch_else(x)         # `try throw(0) catch e; 1 else 2 end`
    try
        x > 0 && jl_throw(x)
    catch e
        1
    else
        2
    end
end
function jl_throw_catch_else_finally(x) # `try throw(0) catch e; 1 else 2 finally 3 end`
    try
        x > 0 && jl_throw(x)
    catch e
        1
    else
        2
    finally
        jl_log(3)
    end
end
function jl_finally_before_catch(x)     # `try throw(0) finally 1 catch e; 2 end`
    try
        x > 0 && jl_throw(x)
        0
    finally
        jl_log(1)
    catch e
        2
    end
end
function jl_catch_rethrow_e(x)          # compat.jl's harness: `catch e; ...; rethrow(e)`
    try
        jl_f(x)
    catch e
        jl_log(:caught)
        x > 15 && rethrow(e)
        -1
    end
end

# exceptions_ir.jl
function jl_return_try_catch(x)         # "Return from inside try/catch"
    try
        jl_f(x)
        return x
    catch
        jl_g(x - 20)
        return -x
    end
end
function jl_return_try_catch_const(x)   # "... with simple return vals"
    try
        jl_f(x)
        return 10
    catch
        jl_log(:g)
        return 20
    end
end
function jl_return_multi_try(x)         # "Return from multiple try + try/catch"
    try
        try
            jl_f(x)
            return 10
        catch
            jl_g(x - 20)
            return 20
        end
    catch
    end
end
function jl_return_multi_catch(x)       # "Return from multiple catch + try/catch"
    try
        jl_f(x)
    catch
        try
            jl_g(x - 20)
            return 10
        catch
            return 20
        end
    end
end
function jl_try_else_stmt(x)            # "try/catch/else, not value/tail"
    try
        jl_f(x)
    catch
        jl_log(:b)
    else
        jl_log(:c)
    end
    x * 3
end
function jl_finally_stmt(x)             # "basic try/finally, not value/tail"
    try
        jl_f(x)
    finally
        jl_log(x)
    end
    x * 3
end
function jl_finally_break(x)            # "try/finally + break"
    while true
        try
            jl_f(x)
            break
        finally
            jl_log(x)
        end
    end
    x
end
function jl_nested_finally_return(x)    # "Nested finally blocks"
    try
        try
            if x > 5
                return jl_f(x)
            end
            jl_g(x)
        finally
            jl_log(:c)
        end
    finally
        jl_log(:d)
    end
end
jl_exc_object(x) = try jl_f(x) catch exc; jl_log(exc); 0 end          # "Access to the exception object"

# demo.jl
function jl_nested_catch_else(x::Int, y::Bool)
    z = try
        try
            jl_f(x)
            1
        catch exc
            if y
                return 2
            end
            jl_g(x - 20)
            3
        else
            4
        end
    catch
        5
    end
    z
end
function jl_let_nested_finally_return(x)
    try
        try
            return jl_f(x)
        finally
            jl_log(1)
        end
    finally
        jl_log(2)
    end
    x
end
function jl_goto_retry(n)               # `@label foo; try ... @goto foo catch ... @goto foo end`
    i = n
    j = 1
    @label foo
    try
        jl_log(i)
        i = jl_f(i)
        if i <= 2
            @goto foo
        end
    catch exc
        j = j + 1
        if j <= 2
            i -= 9
            @goto foo
        end
    end
    (i, j)
end

# destructuring.jl: no assignment happens when the right-hand side throws.
function jl_destructure_throw(x)
    local a
    p, q, r = 1, 2, 3
    side = false
    x > 0 && (a = x)
    exc = try
        f() = (side = true)
        (p, q, r) = (100, a, f())
        nothing
    catch e
        e isa UndefVarError
    end
    (p, q, r, side, exc)
end
function jl_destructure_isdefined(x)
    local p, q, a
    x > 0 && (a = x)
    try
        (p, q) = (1, a)
    catch
    end
    @isdefined(p)
end

#=============================================================================
 Nested trys, exits across trys, finally with return/break, rethrow
=============================================================================#

# (added) `continue`/`break` across two trys, finally on the way out.
function jl_continue_nested_finally(n)
    s = 0
    for i in 1:n
        try
            try
                isodd(i) && continue
                s += jl_f(i)
            finally
                jl_log(i)
            end
        catch
            s -= 1
        end
    end
    s
end
function jl_break_nested_finally(n)
    s = 0
    i = 0
    while true
        i += 1
        try
            try
                s += jl_f(i)
                s > n && break
            finally
                jl_log(-i)
            end
        catch
            break
        end
    end
    (s, i)
end
# (added) `break` and `return` from inside finally (allowed, if unusual).
function jl_break_in_finally(n)
    s = 0
    for i in 1:n
        try
            s += jl_f(i)
        finally
            i == 3 && break
        end
    end
    s
end
function jl_return_in_finally(x)
    try
        jl_f(x)
    finally
        x > 5 && return -x
    end
end
# (added) `@goto` from an inner try or its catch to a label in the outer try.
function jl_goto_between_trys(x)
    try
        try
            jl_f(x)
            x > 5 && @goto mid
            jl_log(1)
        catch
            jl_log(2)
            @goto mid
        end
        jl_log(3)
        @label mid
        jl_g(x - 15)
    catch
        -1
    end
end
# (added) a rethrow from a nested catch, caught by the outer try.
function jl_nested_rethrow(x)
    try
        try
            jl_f(x)
        catch e
            x > 15 && rethrow()
            jl_g(x - 13)
        end
    catch e
        e isa DomainError ? -2 : -1
    end
end
# (added) catch inside finally inside catch.
function jl_catch_in_finally(x)
    try
        jl_f(x)
    catch
        try
            jl_g(-x)
        finally
            try
                jl_f(x - 5)
            catch
                jl_log(:inner)
            end
        end
    end
end
# (added) values live into a catch from inside a loop inside the try.
function jl_live_into_catch_loop(n)
    s = 0
    last = 0
    try
        for i in 1:n
            last = i
            s += jl_f(i)
        end
    catch
        return (s, last, -1)
    end
    (s, last, 0)
end
# (added) the caught exception is used after the try.
function jl_exc_after_try(x)
    caught = nothing
    try
        jl_f(x)
    catch e
        caught = e
    end
    caught === nothing ? 0 : caught
end
# (added) `return` from a catch nested two catches deep inside an outer try: the
# exit leaves the outer try, then pops both exceptions.
function jl_return_two_catches_deep(x)
    try
        try
            jl_f(x)
        catch
            try
                jl_g(x - 15)
            catch
                return -length(current_exceptions())
            end
        end
    catch
        return -100
    end
    length(current_exceptions())
end
function jl_return_three_catches_deep(x)
    try
        try
            jl_f(x)
        catch
            try
                jl_g(x - 15)
            catch
                try
                    jl_g(x - 25)
                catch
                    x > 11 && return -length(current_exceptions())
                end
            end
        end
        jl_f(x - 20)
    catch
        return -100
    end
    length(current_exceptions())
end
# (added) `return`, `break` and `continue` all leaving through one finally.
function jl_finally_all_exits(n)
    for i in 1:n
        try
            try
                i == 2 && n > 4 && return i
                i == 3 && break
                isodd(i) && continue
                jl_f(i * 3)
            finally
                jl_log(i)
            end
        catch
            jl_log(-i)
        end
    end
    -1
end
# (added) a variable assigned in an inner try and its catch, read in the outer catch.
function jl_upsilon_through_catch(x)
    y = 0
    try
        try
            y = 1
            jl_f(x)
            y = 2
        catch
            y = 3
            jl_g(-x)
            y = 4
        end
        y = 5
        jl_f(x - 5)
    catch
        return y
    end
    y
end
# (added) a try whose result is a Union.
function jl_try_union(x)
    r = try
        x > 5 ? jl_f(x) : nothing
    catch
        missing
    end
    r === nothing ? -1 : r === missing ? -2 : r
end
# (added) `Base.wait_forever`'s shape: a loop around a try whose body never
# completes normally, so all code after the handler is dominated by the catch.
function jl_endless_try_body(n)
    i = 0
    k = 0
    while true
        try
            while true
                i = jl_f(i)
            end
        catch
            k += 1
            k > n && return (i, k)
            i = k
        end
    end
end
function jl_try_always_throws(n)
    s = 0
    for i in 1:n
        try
            jl_log(i)
            jl_error("always")
        catch
            s += i
        end
    end
    s
end
function jl_after_throwing_try(x)
    try
        jl_error("x")
    catch
        jl_log(1)
    end
    x > 2 ? jl_f(x) : jl_g(x)
end
function jl_throwing_try_two_exits(x)
    x < -5 && @goto big
    if x > 0
        try
            jl_log(x)
            jl_error("x")
        catch
        end
        x > 5 && @goto big
    end
    return 0
    @label big
    return 1
end
# (added) a closure capturing (and boxing) a variable assigned in a catch.
function jl_closure_catch(x)
    y = 0
    get_y() = y
    try
        jl_f(x)
    catch
        y = -1
    end
    get_y() + y
end
# (added) a try in a short-circuit while condition.
function jl_while_and_try(n)
    i = 0
    while i < n && (try jl_f(2i) > 0 catch; false end)
        i += 1
    end
    i
end
function jl_cond_in_try(x)
    try
        if x > 0 && jl_f(x) > 5 || x < -5
            return 1
        end
        0
    catch
        -1
    end
end

# branching_ir.jl "Jumping out of try and catch blocks using @goto"
function jl_goto_out_of_try_catch(x)
    try
        jl_f(x)
        x > 5 && @goto lab
        jl_log(:b)
    catch
        jl_log(:c)
        x > 15 && @goto lab
        jl_log(:d)
    end
    return 0
    @label lab
    return 1
end
# branching_ir.jl "Jumping out of nested try/catch and catch/try"
function jl_goto_out_nested(x)
    try
        try
            jl_f(x)
        catch
            jl_log(:b)
            x > 15 && @goto lab
            jl_log(:c)
        end
        jl_g(x - 30)
    catch
        try
            jl_log(:d)
            x > 25 && @goto lab
            jl_g(-x)
        catch
        end
    end
    return 0
    @label lab
    return 1
end
# (added) a try inside an irreducible loop.
function jl_irreducible_try(x)
    i = 0
    x > 0 && @goto b
    @label a
    i += 1
    @label b
    try
        i = jl_f(i)
    catch
        return -i
    end
    i < x && @goto a
    i
end
# (added) an irreducible loop inside a try body.
function jl_irreducible_in_try(x)
    try
        i = 0
        x > 0 && @goto b
        @label a
        i = jl_f(i)
        @label b
        i += 2
        i < x && @goto a
        i
    catch
        -1
    end
end
# (added) a catch that jumps into the middle of an irreducible loop.
function jl_irreducible_catch_entry(x)
    i = 0
    try
        jl_f(x)
    catch
        @goto b
    end
    @label a
    i += 1
    @label b
    i += 2
    i < 20 && @goto a
    i
end
# (added) the body and the catch enter an irreducible loop at different labels.
function jl_irreducible_two_try_exits(x)
    i = x
    try
        i = jl_f(x)
        @goto a
    catch
        @goto b
    end
    @label a
    i += 1
    jl_log(i)
    @label b
    i += 2
    i < 30 && @goto a
    i
end
# (added) a try in each half of an irreducible loop.
function jl_irreducible_two_trys(x)
    i = 0
    x > 3 && @goto b
    @label a
    try
        i = jl_f(i)
    catch
        i = 2i
    end
    @label b
    try
        i = jl_g(i - 7) ÷ 2 + 1
    catch
        return -i
    end
    i < x && @goto a
    i
end
function jl_while_try_cond(n)
    i = 0
    while (try jl_f(i) catch; 100 end) < n
        i += 1
    end
    i
end

# (added) trys and loops nested every way, with values crossing both.
function jl_try_for_try(n)
    s = 0
    try
        for i in 1:n
            try
                s += jl_f(i)
            catch
                s += jl_g(5 - i)
            end
        end
    catch
        s = -s
    end
    s
end
function jl_try_while_goto(n)           # `@goto` out of a loop and a try
    i = 0
    try
        while true
            i += 1
            for j in 1:i
                j * i > n && @goto done
            end
            jl_f(i)
        end
    catch
        return -i
    end
    @label done
    i
end
jl_gen_in_try(n) = try sum(jl_f(x) for x in 1:n; init=0) catch; -1 end
function jl_closure_try(x)
    h = @inline y -> try jl_f(y) catch; -y end      # inlined: the trys are in this IR
    h(x) + h(x + 5)
end
# (added) `local` in a loop body, assigned in a catch.
function jl_local_in_loop_catch(n)
    s = 0
    for i in 1:n
        local t
        try
            jl_f(3i)
        catch
            t = i
        end
        s += @isdefined(t) ? t : 0
    end
    s
end
function jl_global_try(n)
    global jl_untyped = 0
    for i in 1:n
        try
            jl_untyped += jl_f(i)
        catch
            jl_untyped = -jl_untyped
        end
    end
    jl_untyped
end

#=============================================================================
 ScopedValues and other EnterNode scopes (added: the suite has none)
=============================================================================#

function jl_with_nested(x)
    @with JL_SV => x begin
        a = jl_readsv()
        @with JL_SV => x + 1 begin
            a + jl_readsv() + jl_f(x)
        end
    end
end
jl_with_two(x) = @with JL_SV => x JL_SV2 => 2x begin; jl_readsv() + jl_readsv2() end
function jl_with_in_loop(n)
    s = 0
    for i in 1:n
        s += @with JL_SV => i jl_readsv()
    end
    s
end
function jl_with_in_try(x)
    try
        @with JL_SV => x begin
            jl_f(jl_readsv())
        end
    catch
        jl_readsv()
    end
end
function jl_try_in_with(x)
    @with JL_SV => x begin
        try
            jl_f(x)
        catch
            -jl_readsv()
        end
    end
end
function jl_with_return(x)
    r = @with JL_SV => x begin
        x > 5 && return jl_readsv() * 2
        jl_f(x)
    end
    r + jl_readsv()
end
function jl_with_break(n)
    s = 0
    for i in 1:n
        @with JL_SV => i begin
            s += jl_readsv()
            s > 10 && break
        end
    end
    (s, jl_readsv())
end
jl_with_function(x) = @inline with(() -> jl_readsv() + jl_f(x), JL_SV => x)
function jl_with_in_catch(x)
    try
        jl_f(x)
    catch
        @with JL_SV => -x begin
            jl_readsv()
        end
    end
end

#----------------------------------------------------------------------------- cases

const JL_EH_CASES = Any[
    # try/catch/else/finally
    (jl_try_tail, JL_INTS), (jl_try_error_tail, JL_INTS), (jl_try_catch_exc, JL_INTS),
    (jl_try_else_tail, JL_INTS), (jl_try_return_then_return, JL_INTS),
    (jl_try_return_fallthrough, JL_INTS), (jl_while_catch_break, JL_INTS),
    (jl_while_try_break, JL_INTS), (jl_try_value_exc, JL_INTS),
    (jl_try_value_else, JL_INTS), (jl_try_assign, JL_INTS), (jl_try_assign_exc, JL_INTS),
    (jl_try_assign_else, JL_INTS), (jl_exception_stack, JL_INTS),
    (jl_exception_stack_balanced, JL_INTS), (jl_finally_assign, JL_INTS),
    (jl_try_finally_in_try, JL_INTS),
    (jl_nested_finally, [(true, 5), (true, 100), (false, 5), (false, 100)]),
    (jl_try_catch_finally, JL_INTS), (jl_catch_else_finally, JL_INTS),
    (jl_throw_catch, JL_INTS), (jl_try_finally_value, JL_INTS),
    (jl_throw_catch_finally, JL_INTS), (jl_throw_catch_else, JL_INTS),
    (jl_throw_catch_else_finally, JL_INTS), (jl_finally_before_catch, JL_INTS),
    (jl_catch_rethrow_e, JL_INTS), (jl_return_try_catch, JL_INTS),
    (jl_return_try_catch_const, JL_INTS), (jl_return_multi_try, JL_INTS),
    (jl_return_multi_catch, JL_INTS), (jl_try_else_stmt, JL_INTS),
    (jl_finally_stmt, JL_INTS), (jl_finally_break, JL_INTS),
    (jl_nested_finally_return, JL_INTS), (jl_exc_object, JL_INTS),
    (jl_nested_catch_else, [(x, y) for x in (1, 12, 25) for y in (false, true)]),
    (jl_let_nested_finally_return, JL_INTS), (jl_goto_retry, JL_INTS),
    (jl_destructure_throw, JL_INTS), (jl_destructure_isdefined, JL_INTS),
    # nested trys, exits across trys, rethrow
    (jl_continue_nested_finally, JL_SMALL), (jl_break_nested_finally, JL_SMALL),
    (jl_break_in_finally, JL_SMALL), (jl_return_in_finally, JL_INTS),
    (jl_goto_between_trys, JL_INTS), (jl_nested_rethrow, JL_INTS),
    (jl_catch_in_finally, JL_INTS), (jl_live_into_catch_loop, JL_SMALL),
    (jl_exc_after_try, JL_INTS), (jl_return_two_catches_deep, JL_INTS),
    (jl_return_three_catches_deep, JL_INTS), (jl_finally_all_exits, JL_SMALL),
    (jl_upsilon_through_catch, JL_INTS), (jl_try_union, JL_INTS),
    (jl_closure_catch, JL_INTS), (jl_while_and_try, JL_INTS),
    (jl_endless_try_body, JL_SMALL), (jl_try_always_throws, JL_SMALL),
    (jl_after_throwing_try, JL_INTS), (jl_throwing_try_two_exits, JL_INTS),
    # branching, short-circuit, goto
    (jl_cond_in_try, JL_INTS), (jl_goto_out_of_try_catch, JL_INTS),
    (jl_goto_out_nested, JL_INTS), (jl_irreducible_try, JL_INTS),
    (jl_irreducible_in_try, JL_INTS), (jl_irreducible_catch_entry, JL_INTS),
    (jl_irreducible_two_try_exits, JL_INTS), (jl_irreducible_two_trys, JL_INTS),
    # loops
    (jl_while_try_cond, JL_INTS), (jl_try_for_try, JL_SMALL),
    (jl_try_while_goto, [(0,), (5,), (20,), (60,), (200,)]),
    # generators, comprehensions, closures
    (jl_gen_in_try, JL_SMALL), (jl_closure_try, JL_INTS),
    # scoping
    (jl_local_in_loop_catch, JL_SMALL), (jl_global_try, JL_SMALL),
    # ScopedValues
    (jl_with_nested, JL_INTS), (jl_with_two, JL_INTS), (jl_with_in_loop, JL_SMALL),
    (jl_with_in_try, JL_INTS), (jl_try_in_with, JL_INTS), (jl_with_return, JL_INTS),
    (jl_with_break, JL_SMALL), (jl_with_function, JL_INTS), (jl_with_in_catch, JL_INTS),
]

# Cases whose trys are in a closure the caller inlines.
const JL_INLINED_TRYS = (jl_closure_try, jl_with_function)

@testset "JuliaLowering try/catch cases" begin

# The returns from catches two and three deep run (x = 12: all three calls throw).
# They count the whole exception stack, which on Julia 1.11 also holds the
# exceptions earlier tests leaked.
let n = length(current_exceptions())
    @test jl_return_two_catches_deep(12) == -(n + 2)
    @test jl_return_three_catches_deep(12) == -(n + 3)
end

@testset "$(nameof(f))" for (f, inputs) in JL_EH_CASES
    for promote in (true, false)
        @test isempty(jl_eh_check(f, inputs; promote))
    end
end

# Less tidy IR, as in test/julialowering_cases.jl. The trys of the closures in
# `JL_INLINED_TRYS` are only in the caller's IR once the closure is inlined, which
# these configurations may not do.
@testset "$(nameof(f)), Any arguments" for (f, inputs) in JL_EH_CASES
    @test isempty(jl_eh_check(f, inputs; argtypes=Tuple{map(_ -> Any, first(inputs))...},
                              min_enters=f in JL_INLINED_TRYS ? 0 : 1))
end
@static if VERSION >= v"1.12-"   # the pass numbering of `optimize_until`
    @testset "$(nameof(f)), optimize_until=$stage" for (f, inputs) in JL_EH_CASES, stage in (3, 5)
        @test isempty(jl_eh_check(f, inputs; optimize_until=stage,
                                  min_enters=f in JL_INLINED_TRYS ? 0 : 1))
    end
end

end  # JuliaLowering try/catch cases
