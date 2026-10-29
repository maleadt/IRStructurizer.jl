#=============================================================================
 Control-flow shapes from JuliaLowering.jl's test suite, as round-trip tests.

 The cases come from JuliaLowering.jl's `test/` directory (branching, loops,
 generators, closures, scopes, decls, destructuring, compat and demo). Each snippet
 there evaluates a top-level expression over free globals (`a`, `b`, `f`). Here each
 one is an ordinary function whose arguments pick the path, and the opaque
 operations are `@noinline` calls that can throw or log. A comment names the source
 of each case. Cases marked `(added)` fill in categories the suite only touches,
 such as irreducible loops built from `@goto` and globals in loops. The cases with
 try/catch are in test/julialowering_exceptions.jl, which reuses the helpers and
 the harness defined here.

 Every case is structurized with and without loop promotion and round-tripped by
 `jl_check`: lowered back to `IRCode` (which must pass `verify_ir`) and run on every
 input, directly and from inside a catch, the result, the exceptions a throw leaves
 on the stack, and the `jl_log` side effects must match the direct call. Each case
 also runs with `Any` arguments, and with the optimizer stopped after its first and
 second compaction, to get less tidy IR from the same source.

 Skipped, because they only make sense as lowering-internal or top-level syntax:
 - error cases (`break` outside a loop, undefined or duplicate labels, `@label` as a
   value, bad `let`/`local`/`global` declarations): they never reach `IRCode`;
 - top-level-only forms: soft/neutral/hard scope wrappers on module globals,
   `global` declarations in tail position, `const` and `global f() = ...` method
   definitions in `let`, modules, macros, `@eval`, `include`, typedefs, `@ccall`,
   `@cfunction`, `@islocal`/`@locals`;
 - forms without control flow of their own (named tuples, property access,
   updating and chained assignments, juxtaposition, quoting).
=============================================================================#

using Base.ScopedValues

#----------------------------------------------------------------------------- helpers

const JL_LOG = Any[]
@noinline jl_log(@nospecialize(x)) = (push!(JL_LOG, x); nothing)
"""Throw `e`, logging it first, so a log also records the throws that are caught."""
@noinline jl_throw(@nospecialize(e)) = (push!(JL_LOG, (:throw, rt_payload(e))); throw(e))

# `jl_f` stands for the free calls of the original snippets (`a`, `f`, `g`). It
# throws for x > 10. `jl_g` throws a different exception for x < 0. `jl_error`
# stands for `error`. Every throw goes through `jl_throw`.
@noinline jl_f(x::Int) = x > 10 ? jl_throw(ErrorException("f: $x")) : x + 1
@noinline jl_g(x::Int) = x < 0 ? jl_throw(DomainError(x)) : 2x
jl_error(msg) = jl_throw(ErrorException(msg))
const JL_SV = ScopedValue(1)
const JL_SV2 = ScopedValue(10)
@noinline jl_readsv() = JL_SV[]
@noinline jl_readsv2() = JL_SV2[]
global jl_counter::Int = 0
jl_untyped = 0

#----------------------------------------------------------------------------- harness

"""Structurize `f` at the signature of its inputs (or `argtypes`), lower it back and
compare it with the direct call on every input (`rt_compare`, test/setup.jl).
`optimize_until` stops the optimizer early, as for `code_ircode`. Returns the
problems found."""
function jl_check(f, inputs; promote=true, argtypes=Tuple{map(typeof, first(inputs))...},
                  optimize_until=nothing)
    ir, _ = only(code_ircode(f, argtypes; optimize_until))
    sci = StructuredIRCode(ir; promote)
    return rt_compare(JL_LOG, f, rt_lower(sci), inputs)
end

#=============================================================================
 Branching, short-circuit conditions, symbolic goto
=============================================================================#

# branching.jl "Tail position" / "Value required" / "Side effects"
jl_if_tail(a::Bool) = if a; 1 end
jl_if_else_tail(a::Bool) = if a; 1 else 2 end
jl_elseif_tail(a::Bool, b::Bool) = if a; 1 elseif b; 2 else 3 end
function jl_if_value(a::Bool, b::Bool)
    x = if a
        1
    elseif b
        2
    end
    x
end
function jl_if_side(a::Bool, b::Bool)
    x = nothing
    if a
        x = 1
    elseif b
        x = 2
    else
        x = 3
    end
    x
end
function jl_block_cond(a::Bool)         # `if begin; x = 2; a; end; x end`
    if (x = 2; a)
        x
    end
end

# branching.jl "`&&` and `||` chains"
jl_and_chain(a::Bool, b::Bool) = a && b && "hi"
jl_or_chain(a::Bool, b::Bool) = a || b || "hi"
function jl_and_or_value(a::Bool, b::Bool)
    z = a && "hi"
    w = b || "ho"
    (z, w)
end

# branching_ir.jl "Blocks compile directly to branches": `if (a; b && c) d end`
function jl_block_and_cond(a::Bool, b::Bool, c::Bool)
    if (jl_log(a); b && c)
        jl_log(:d)
    end
end
# (added) nested short-circuits in conditions, around a throwing call.
function jl_complex_cond(x)
    if (x > 3 && isodd(x)) || (x < 0 && jl_g(x) > 0)
        1
    elseif !(x == 2 || x == 4) && jl_f(x) > 5
        2
    else
        3
    end
end

# branching_ir.jl "symbolic goto forward/backward jump"
function jl_goto_forward(x)
    jl_log(1)
    x > 0 && @goto foo
    jl_log(2)
    @label foo
    x
end
function jl_goto_backward(n)            # branching.jl "symbolic goto/label"
    a = Int[]
    i = 1
    @label foo
    push!(a, i)
    i = i + 1
    if i <= n
        @goto foo
    end
    a
end

# (added) irreducible loops built from gotos: a loop with two entries.
function jl_irreducible(x)
    i = 0
    x > 0 && @goto b
    @label a
    i += 1
    jl_log(i)
    @label b
    i += 2
    i < x && @goto a
    i
end

#=============================================================================
 Loops
=============================================================================#

# loops.jl "while loops"
function jl_while_push(n)
    a = Int[]
    i = 0
    while i < n
        i = i + 1
        push!(a, i)
    end
    a
end
function jl_while_break(n)
    a = Int[]
    i = 0
    while i < n
        i = i + 1
        if i == 3
            break
        end
        push!(a, i)
    end
    a
end
function jl_while_continue(n)
    a = Int[]
    i = 0
    while i < n
        i = i + 1
        if isodd(i)
            continue
        end
        push!(a, i)
    end
    a
end
# loops_ir.jl "While loop with short circuit condition"
function jl_while_and(n)
    i = 0
    while i < n && i != 7
        i += 1
    end
    i
end
# loops_ir.jl "While loop with with break and continue" (dead code after both)
function jl_while_break_continue(n)
    i = 0
    while i < n
        i += 1
        jl_log(1)
        i > 3 && break
        jl_log(2)
        isodd(i) && continue
        jl_log(3)
    end
    i
end
# (added) complex while conditions: a block, `||` of calls, a try.
function jl_while_complex(n)
    i = 0
    s = 0
    while (i += 1; i < n) && (isodd(i) || i % 3 == 0 || jl_f(i) < 5)
        s += i
    end
    (i, s)
end

# loops.jl "for loops"
function jl_for_push(n)
    a = Int[]
    for i = 1:n
        push!(a, i)
    end
    a
end
function jl_for_underscore(n)
    a = Int[]
    for _ = 1:n
        push!(a, 1)
    end
    a
end
function jl_for_break(n)
    a = Int[]
    for i = 1:n
        if i == 3
            break
        end
        push!(a, i)
    end
    a
end
function jl_for_nested_break(n)          # "Break from inner nested loop"
    a = Tuple{Int,Int}[]
    for i in 1:n
        for j in 3:6
            push!(a, (i, j))
            j == 4 && break
        end
    end
    a
end
function jl_for_continue(n)
    a = Int[]
    for i = 1:n
        if isodd(i)
            continue
        end
        push!(a, i)
    end
    a
end
function jl_for_loopvar_assign(n)       # "Loop variable scope"
    a = Int[]
    for i = 1:n
        push!(a, i)
        i = 100
    end
    a
end
function jl_for_shadow(n)
    i = 100
    for i = 1:n
    end
    i
end
function jl_for_outer(n)
    i = 100
    for outer i = 1:n
        nothing
    end
    i
end
function jl_for_destructure(n)          # "Fancy for loop left hand side"
    a = Tuple{Int,Int}[]
    i = 100
    j = 200
    for (i, j) in [(1, 2), (n, 2n)]
        push!(a, (i, j))
    end
    (a, i, j)
end
function jl_for_number(n)               # compat.jl `for x in 1; x+=1; if true continue elseif false break end end`
    s = 0
    for x in n
        x += 1
        if x > 3
            s += x
            continue
        elseif x < 0
            break
        end
        s -= 1
    end
    s
end

# loops.jl "multidimensional for loops"
function jl_for2(n)
    a = Tuple{Int,Int}[]
    for i = 1:n, j = 3:4
        push!(a, (i, j))
    end
    a
end
function jl_for2_break(n)
    a = Tuple{Int,Int}[]
    for i = 1:n, j = 3:4
        push!(a, (i, j))
        break
    end
    a
end
function jl_for2_continue_outer(n)
    a = Tuple{Int,Int}[]
    for i = 1:n, j = 3:4
        if isodd(i)
            continue
        end
        push!(a, (i, j))
    end
    a
end
function jl_for2_continue_inner(n)
    a = Tuple{Int,Int}[]
    for i = 1:2, j = 1:n
        if isodd(j)
            continue
        end
        push!(a, (i, j))
    end
    a
end
function jl_for2_loopvar(n)
    a = Tuple{Int,Int}[]
    for i = 1:n, j = 3:4
        push!(a, (i, j))
        i = 100
    end
    a
end
function jl_for2_outer(n)
    i = 100
    j = 200
    for outer i = 1:n, j = 3:4
        nothing
    end
    (i, j)
end
function jl_for2_outer_inner(n)
    i = 100
    j = 200
    for i = 1:2, outer j = 3:n
        nothing
    end
    (i, j)
end
# loops_ir.jl "Syntax sugar for nested for loop" (assigning a copy of `x`)
function jl_for2_copy(n)
    s = 0
    for x in 1:n, y in 1:2
        x = 10
        s += x + y
    end
    s
end

#=============================================================================
 Generators, comprehensions, closures
=============================================================================#

# generators.jl
jl_gen_sq(n) = collect(x^2 for x in 1:n)
jl_gen_filter(n) = collect(x for x in 1:n if isodd(x))
jl_gen_zip(n) = collect((y, x) for (x, y) in zip(1:n, 2:n+1) if y != 3)
jl_gen_product(n) = collect((x, y) for x in 1:n, y in 1:2)
jl_gen_flatten(n) = collect((x, y, z) for x in 1:n, y in 4:5 for z in 6:7)
jl_gen_dup(n) = collect(x for x in 1:n for x in 1:2)
jl_gen_protect(n) = collect((z = y; y = 100; z) for y in 1:n for x in 1:2)
jl_typed_comp(n) = Tuple{Int,Int}[(x, y) for x in 1:2, y in 1:n]
jl_comp3(n) = [(x, y, z) for x in 1:n for y in 4:5 for z in 6:7]
jl_typed_comp_filter(n) = Int[x + y for x in 1:n, y in 3:4 if isodd(x + y)]   # compat.jl
# (added) a throwing comprehension, and a generator inside a try.
jl_comp_throw(n) = [jl_f(x) for x in 1:n]

# closures_ir.jl / closures.jl
function jl_closure_assign(x)           # "arguments are captured into a closure and assigned"
    g() = (x = 10)
    x > 5 && g()
    x
end
function jl_closure_isdefined(x)        # "Closure captures with `isdefined`"
    function g()
        z = 3
        (@isdefined(x), @isdefined(y), @isdefined(z))
    end
    r1 = g()
    x > 0 && (y = 2)
    (r1, g(), @isdefined(y), @isdefined(x))
end
function jl_closure_typed(x)            # "Closure capturing a typed local"
    T = Float64
    y::T = x
    f() = (y = 2.0)
    x > 0 && f()
    y
end
function jl_mutual_recursion(n)         # "Mutually recursive closures"
    ra(k) = k <= 0 ? 0 : rb(k - 1) + 1
    rb(k) = k <= 0 ? 0 : ra(k - 1) + 2
    ra(n)
end
jl_do_block(n) = map(1:n) do y          # "`do` blocks"
    y > 3 ? y + 2 : y
end
jl_anon(x) = (y -> y * y)(x)            # "Anonymous function syntax with ->"
# (added) closures with control flow of their own, inlined into the caller.
function jl_closure_control(n)
    acc = 0
    add(i) = isodd(i) ? (acc += i) : (acc -= 1)
    for i in 1:n
        add(i)
    end
    acc
end

#=============================================================================
 Scoping: let, local, global, typed declarations
=============================================================================#

function jl_let_shadow(x)               # scopes.jl `let x = x + 1; y = x end`
    y = 0
    let x = x + 1
        y = x
    end
    (x, y)
end
function jl_let_rebind(x)               # scopes_ir.jl `let x = f(x), x = g(x) end`
    let x = jl_f(x), x = jl_g(x - 5)
        x
    end
end
function jl_let_closure_outer(x)        # scopes.jl: a closure in `let` sees the outer `y`
    y = x
    let f() = y
        y2 = -x
        f() + y2
    end
end
function jl_arg_decl(x)                 # decls_ir.jl "Type decl on function argument"
    x::Int = x
    x = x / 2
    x
end
function jl_typed_local(x)              # assignments_ir.jl "declarations of typed locals"
    local y::Int = jl_f(x)
    y = y / 2
    y
end
# (added) `local` in a loop body is fresh in every iteration.
function jl_local_in_loop(n)
    s = 0
    for i in 1:n
        local t
        if isodd(i)
            t = i
        end
        s += @isdefined(t) ? t : 100
    end
    s
end
# (added) typed and untyped globals updated in loops.
function jl_global_in_loop(n)
    global jl_counter = 0
    for i in 1:n
        jl_counter += i
    end
    jl_counter
end

#=============================================================================
 Misc
=============================================================================#

function jl_preserve(x)                 # misc_ir.jl "GC.@preserve support"
    a = Ref(x)
    GC.@preserve a begin
        x > 0 ? a[] + 1 : jl_g(x)
    end
end

#----------------------------------------------------------------------------- cases

const JL_INTS = [(0,), (1,), (3,), (7,), (12,), (20,), (30,), (-3,)]
const JL_BOOLS2 = [(a, b) for a in (false, true) for b in (false, true)]
const JL_SMALL = [(0,), (1,), (3,), (6,), (12,)]

const JL_CASES = Any[
    # branching, short-circuit, goto
    (jl_if_tail, [(false,), (true,)]), (jl_if_else_tail, [(false,), (true,)]),
    (jl_elseif_tail, JL_BOOLS2), (jl_if_value, JL_BOOLS2), (jl_if_side, JL_BOOLS2),
    (jl_block_cond, [(false,), (true,)]), (jl_and_chain, JL_BOOLS2),
    (jl_or_chain, JL_BOOLS2), (jl_and_or_value, JL_BOOLS2),
    (jl_block_and_cond, [(a, b, c) for a in (false, true) for b in (false, true) for c in (false, true)]),
    (jl_complex_cond, JL_INTS), (jl_goto_forward, JL_INTS), (jl_goto_backward, JL_SMALL),
    (jl_irreducible, JL_INTS),
    # loops
    (jl_while_push, JL_SMALL), (jl_while_break, JL_SMALL), (jl_while_continue, JL_SMALL),
    (jl_while_and, JL_INTS), (jl_while_break_continue, JL_SMALL),
    (jl_while_complex, JL_INTS), (jl_for_push, JL_SMALL), (jl_for_underscore, JL_SMALL),
    (jl_for_break, JL_SMALL), (jl_for_nested_break, JL_SMALL), (jl_for_continue, JL_SMALL),
    (jl_for_loopvar_assign, JL_SMALL), (jl_for_shadow, JL_SMALL), (jl_for_outer, JL_SMALL),
    (jl_for_destructure, JL_SMALL), (jl_for_number, JL_INTS), (jl_for2, JL_SMALL),
    (jl_for2_break, JL_SMALL), (jl_for2_continue_outer, JL_SMALL),
    (jl_for2_continue_inner, JL_SMALL), (jl_for2_loopvar, JL_SMALL),
    (jl_for2_outer, JL_SMALL), (jl_for2_outer_inner, JL_SMALL), (jl_for2_copy, JL_SMALL),
    # generators, comprehensions, closures
    (jl_gen_sq, JL_SMALL), (jl_gen_filter, JL_SMALL), (jl_gen_zip, JL_SMALL),
    (jl_gen_product, JL_SMALL), (jl_gen_flatten, JL_SMALL), (jl_gen_dup, JL_SMALL),
    (jl_gen_protect, JL_SMALL), (jl_typed_comp, JL_SMALL), (jl_comp3, JL_SMALL),
    (jl_typed_comp_filter, JL_SMALL), (jl_comp_throw, JL_SMALL),
    (jl_closure_assign, JL_INTS), (jl_closure_isdefined, JL_INTS),
    (jl_closure_typed, JL_INTS), (jl_mutual_recursion, JL_SMALL), (jl_do_block, JL_SMALL),
    (jl_anon, JL_INTS), (jl_closure_control, JL_SMALL),
    # scoping
    (jl_let_shadow, JL_INTS), (jl_let_rebind, JL_INTS), (jl_let_closure_outer, JL_INTS),
    (jl_arg_decl, JL_INTS), (jl_typed_local, JL_INTS), (jl_local_in_loop, JL_SMALL),
    (jl_global_in_loop, JL_SMALL),
    # misc
    (jl_preserve, JL_INTS),
]

@testset "round-trip harness" begin
    # `rethrow(e)` in a catch replaces the exception without growing the stack; the
    # outcome still tells the two apart.
    rethrow_a() = rethrow(ErrorException("A"))
    rethrow_b() = rethrow(ErrorException("B"))
    @test rt_outcome_in_catch(JL_LOG, rethrow_a) != rt_outcome_in_catch(JL_LOG, rethrow_b)
end

@testset "JuliaLowering control-flow cases" begin

@testset "$(nameof(f))" for (f, inputs) in JL_CASES
    for promote in (true, false)
        @test isempty(jl_check(f, inputs; promote))
    end
end

# The same cases in less tidy IR. With `Any` arguments, dispatch is dynamic and phis
# are typed narrower than the values that feed them. Stopping the optimizer after
# its first or second compaction (before or after inlining) keeps the redundant
# blocks, `isa`/`=== nothing` refinements and unions it would later fold away.
@testset "$(nameof(f)), Any arguments" for (f, inputs) in JL_CASES
    @test isempty(jl_check(f, inputs; argtypes=Tuple{map(_ -> Any, first(inputs))...}))
end
@static if VERSION >= v"1.12-"   # the pass numbering of `optimize_until`
    @testset "$(nameof(f)), optimize_until=$stage" for (f, inputs) in JL_CASES, stage in (3, 5)
        @test isempty(jl_check(f, inputs; optimize_until=stage))
    end
end

end  # JuliaLowering control-flow cases
