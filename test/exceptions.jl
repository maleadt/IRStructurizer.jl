#=============================================================================
 Exception handling: EnterNode / :leave / PhiC+Upsilon, lifted with
 `exceptions=:structured`.

 The shapes below are functions with try/catch. The testsets check the MCFG that
 `ingest(ir; exceptions=:structured)` and `normalize_cf!` build from them.
=============================================================================#

using IRStructurizer: ingest, handler_stacks, is_leave, MEnter, try_info, try_exit_refs,
                      edge_of, is_pop_exception
using Base.ScopedValues

const EH_LOG = Any[]
@noinline eh_log(@nospecialize(x)) = (push!(EH_LOG, x); nothing)
"""Throw `e`, logging it first. The test functions throw through this, so a log
also records the throws that a handler catches."""
@noinline eh_throw(@nospecialize(e)) = (push!(EH_LOG, (:throw, rt_payload(e))); throw(e))
@noinline eh_g(x::Int) = x > 10 ? eh_throw(ErrorException("big")) : x + 1
@noinline eh_h(x::Int) = x < 0 ? eh_throw(DomainError(x)) : x * 2
const EH_SV = ScopedValue(1)
@noinline eh_readsv() = EH_SV[]

#----------------------------------------------------------------------------- shapes

eh_basic(x) = try eh_g(x) catch; -1 end
eh_exc(x) = try eh_g(x) catch e; e end
function eh_finally(x)
    r = 0
    try
        r = eh_g(x)
    finally
        r += 100
    end
    r
end
function eh_nested(x)
    try
        a = eh_g(x)
        try
            eh_h(a - 8)
        catch
            a - 5
        end
    catch
        -1
    end
end
function eh_upsilon(x)
    y = 0
    try
        y = x + 1
        y = eh_g(y)
        y = eh_h(y - 20)
    catch
        return y
    end
    y
end
eh_rethrow(x) = try eh_g(x) catch; x > 15 && rethrow(); -x end
function eh_return_in_try(x)
    try
        y = eh_g(x)
        if y > 5
            return y
        end
        eh_h(y - 3)
    catch
        0
    end
end
function eh_mixed_exit(x)   # an exit nested in an arm whose sibling stays in the try
    try
        if x > 0
            if x > 5
                return x * 3
            end
            y = eh_g(x)
        else
            y = eh_h(x)
        end
        y + 1
    catch
        -7
    end
end
function eh_dead_merge(x)   # an exit next to a throwing merge inside the try
    try
        if x > 3
            z = 1
        elseif x > 1
            return eh_g(x)
        else
            z = 2
        end
        eh_throw(ErrorException("boom $z"))
    catch
        -9
    end
end
function eh_nested_return(x)   # `return` pops two handlers; pop_exception after leave
    try
        try
            return eh_g(x)
        catch
            return eh_h(x)
        end
    catch
        return 0
    end
end
function eh_try_in_loop(n)
    s = 0
    for i in 1:n
        try
            s += eh_g(i)
        catch
            s -= 1
        end
    end
    s
end
function eh_loop_in_try(n)
    try
        s = 0
        for i in 1:n
            s += eh_g(i)
        end
        s
    catch
        -1
    end
end
function eh_break_in_try(n)
    s = 0
    i = 0
    while true
        i += 1
        try
            s += eh_g(i)
            s > n && break
        catch
            s = -s
            break
        end
    end
    s
end
function eh_continue_from_catch(n)
    s = 0
    i = 0
    while i < n
        i += 1
        try
            s += eh_g(i * 3)
        catch
            continue
        end
        s += 1
    end
    s
end
function eh_throw_in_loop_in_try(n)
    try
        s = 0
        for i in 1:n
            i == 7 && eh_throw(ArgumentError("seven"))
            s += i
        end
        s
    catch e
        e isa ArgumentError ? -7 : -1
    end
end
function eh_throw_in_try_in_loop(n)
    s = 0
    i = 0
    while i < n
        i += 1
        try
            i == 3 && eh_throw(ArgumentError("three"))
            s += i
        catch
            s -= 100
        end
    end
    s
end
function eh_return_from_inner_catch(n)   # inner catch returns out of a loop and an outer try
    try
        s = eh_h(n)
        for i in 1:n
            try
                s += eh_g(i)
            catch
                return -s
            end
        end
        s + eh_h(n - 20)
    catch
        -1
    end
end
function eh_finally_break(n)
    s = 0
    for i in 1:n
        try
            s += eh_g(i)
            s > 10 && break
        finally
            eh_log(i)
        end
    end
    s
end
function eh_finally_return(x)
    try
        return eh_g(x)
    catch
        return -1
    finally
        x > 100 && eh_log(x)
    end
end
function eh_try_in_catch(n)
    s = 0
    for i in 1:n
        try
            s += eh_g(i)
        catch
            try
                s += eh_h(-i)
            catch
                s -= 1
            end
        end
    end
    s
end
function eh_three_levels(x)
    try
        a = eh_g(x)
        try
            b = eh_h(a - 8)
            try
                eh_g(b)
            catch
                b + 1000
            end
        catch
            a + 100
        end
    catch
        -1
    end
end
function eh_sequential(x)
    a = try eh_g(x) catch; 1 end
    b = try eh_h(x - 5) catch; 2 end
    a + b
end
function eh_goto_out(x)
    try
        y = eh_g(x)
        y > 5 && @goto out
        return y
    catch
        return -1
    end
    @label out
    return 1000
end
function eh_lazy(n)   # a variable first defined in a catch: undefined on loop entry
    local acc
    i = 0
    while i < n
        i += 1
        try
            eh_g(i)
        catch
            if !@isdefined(acc)
                acc = Int[]
            end
            push!(acc, i)
        end
    end
    @isdefined(acc) ? length(acc) : 0
end
eh_scoped(x) = @with EH_SV => x begin; eh_readsv() + eh_g(x) end
eh_scope_only(x) = @with EH_SV => x begin; x + 1 end   # nothrow body: EnterNode(0, scope)
# Inlined ScopedValue reads: the phi of the read is narrower than the value
# feeding it (an `Any` yield into an `Int` slot unless narrowed).
eh_scoped_inline(x) = @with EH_SV => x begin; EH_SV[] + eh_g(x) end
eh_scoped_inline_try(x) = try @with EH_SV => x begin; eh_g(EH_SV[]) end catch; EH_SV[] end
# A body that cannot complete normally: the catch dominates everything after it.
function eh_throwing_body_in_loop(n)
    for i in 1:n
        try
            eh_throw(ErrorException("x"))
        catch
        end
    end
    n
end
function eh_throwing_body_two_exits(x)
    x < -5 && @goto big
    if x > 0
        try
            eh_g(x + 20)
        catch
        end
        x > 5 && @goto big
    end
    return 0
    @label big
    return 1
end
# `Base.wait_forever`'s shape: an endless loop around a try whose body is an endless
# loop. Not run, since it never returns.
function eh_endless(x)
    while true
        try
            while true
                eh_log(eh_g(x))
            end
        catch e
            eh_log(e)
        end
    end
end
# Nested exceptions of one type: only the message tells them apart.
function eh_same_type(x)
    try
        try
            eh_throw(ErrorException("inner $x"))
        catch
            x > 5 && eh_throw(ErrorException("outer $x"))
            rethrow()
        end
    catch e
        x > 10 && rethrow()
        (e::ErrorException).msg
    end
end
# An exit out of a try nested in a catch: Julia pops the catch's exception before
# it leaves the nested try, so the leave block is still inside the handler.
function eh_break_from_try_in_catch(x)
    for i in 1:3
        try
            x > i && eh_throw(ErrorException("a $i"))
        catch
            try
                eh_log(i)
                x > 5 && break
            catch
            end
        end
    end
    x
end
function eh_return_from_try_in_catch(x)
    try
        try
            x > 0 && eh_throw(ErrorException("a"))
        catch
            try
                eh_log(9)
                return x
            catch
            end
        end
    finally
        eh_log(1)
    end
    -x
end
# The first try's body always returns, so its catch dominates the second try,
# which must not join the first try's handler.
# A catch that returns out of an enclosing try and a loop: Julia leaves the outer
# try, then pops the inner catch's exception.
function eh_return_from_nested_catch_in_loop(x)
    w = 0
    while w < 3
        w += 1
        try
            try
                x > w && eh_throw(ErrorException("a $w"))
            catch
                x > 5 && return x
            end
            x > 9 && eh_throw(ErrorException("b"))
        catch
        end
    end
    x
end
# A `continue` out of a try nested in a catch: Julia pops the catch's exception,
# then leaves the nested try. The body always throws, so the catch dominates the
# loop's latch.
function eh_continue_from_try_in_catch(x)
    for i in 1:3
        try
            eh_throw(ErrorException("a $i"))
        catch
            try
                x > 4 && eh_throw(ErrorException("b $i"))
                continue
            catch
                eh_log(i)
            end
        end
        eh_log(-i)
    end
    x
end
function eh_continue_from_try_in_catch_in_try(x)
    try
        for i in 1:3
            try
                eh_throw(ErrorException("a $i"))
            catch
                try
                    x > 4 && eh_throw(ErrorException("b $i"))
                    continue
                catch
                    eh_log(i)
                end
            end
            eh_log(-i)
        end
    catch
    end
    x
end
# A `finally` that returns after a throw. Julia 1.11 leaves the exception on the
# exception stack here, in the direct call and the round trip alike.
function eh_return_from_finally(x)
    try
        eh_g(x)
    finally
        x > 5 && return -x
    end
end
# A try nested in a catch, in a loop, whose exits pop the catch's exception at
# different points: the `break` pops it in the nested catch, the `return` after
# leaving the nested try. The nested try's continuation is still in the catch.
function eh_return_or_break_from_try_in_catch(x)
    for i in 1:3
        try
            eh_log(i)
            x > 7 && eh_throw(ErrorException("a $i"))
        catch
            try
                x > -2 && eh_throw(ErrorException("b $i"))
                return x
            catch
                break
            end
        end
    end
    -x
end
# `continue` and `break` from a catch in an inner loop: the inner loop's two exits
# meet in a block with arguments right before the outer back edge.
function eh_exits_from_catch_in_nested_loops(x)
    w = 0
    while w < 3
        w += 1
        v = 0
        while v < 3
            v += 1
            try
                x > 1 && eh_throw(ErrorException("a $v"))
                x += 11
            catch
                x > 7 && break
                x > 5 && continue
                x += 1
            end
        end
    end
    x
end
function eh_try_after_returning_try(x)
    try
        eh_log(10)
        return x
    catch
    end
    try
        x += 1
        eh_log(5)
    catch
    end
    x
end

const EH_CASES = [
    (eh_basic, (1, 20)), (eh_exc, (1, 20)), (eh_finally, (1, 20)), (eh_nested, (1, 5, 20)),
    (eh_upsilon, (1, 15, 20)), (eh_rethrow, (1, 12, 20)), (eh_return_in_try, (1, 7, 20)),
    (eh_mixed_exit, (-3, 0, 2, 7, 20)), (eh_dead_merge, (0, 2, 5, 20)),
    (eh_nested_return, (1, 20, -20)), (eh_try_in_loop, (0, 3, 15)),
    (eh_loop_in_try, (0, 5, 15)), (eh_break_in_try, (3, 20, 100)),
    (eh_continue_from_catch, (0, 2, 6)), (eh_throw_in_loop_in_try, (0, 5, 9)),
    (eh_throw_in_try_in_loop, (0, 2, 5)), (eh_return_from_inner_catch, (0, 3, 15, 25)),
    (eh_finally_break, (0, 3, 15)), (eh_finally_return, (1, 20)),
    (eh_try_in_catch, (0, 5, 15)), (eh_three_levels, (1, 5, 9, 15)),
    (eh_sequential, (1, 3, 20)), (eh_goto_out, (1, 7, 20)), (eh_lazy, (0, 5, 15)),
    (eh_scoped, (3, 20)), (eh_scope_only, (3, 20)),
    (eh_scoped_inline, (3, 20)), (eh_scoped_inline_try, (3, 20)),
    (eh_throwing_body_in_loop, (0, 3)), (eh_throwing_body_two_exits, (-9, -1, 3, 9)),
    (eh_same_type, (1, 7, 12)),
    (eh_break_from_try_in_catch, (-2, 0, 1, 3, 7)),
    (eh_return_from_try_in_catch, (-2, 0, 3)),
    (eh_try_after_returning_try, (0, 3)),
    (eh_return_from_nested_catch_in_loop, (-2, 0, 3, 7, 12)),
    (eh_continue_from_try_in_catch, (-2, 3, 7)),
    (eh_continue_from_try_in_catch_in_try, (-2, 3, 7)),
    (eh_return_from_finally, (1, 7, 12, 20)),
    (eh_return_or_break_from_try_in_catch, (-5, 0, 9)),
    (eh_exits_from_catch_in_nested_loops, (-5, 0, 3, 6, 8)),
]

@testset "exceptions" begin

@testset "ingest: the exceptions keyword" begin
    ir = first(only(code_ircode(eh_basic, (Int,))))
    @test_throws UnstructuredControlFlowError ingest(ir)
    @test_throws ArgumentError ingest(ir; exceptions=:bogus)
    m = ingest(ir; exceptions=:structured)
    @test m.has_eh && count(b -> b.term isa MEnter, m.blocks) == 1
    m = ingest(first(only(code_ircode(x -> x > 0 ? x : -x, (Int,)))); exceptions=:structured)
    @test !m.has_eh
end

@testset "an upsilon in a dead block leaves its PhiC" begin
    # Block 3 is unreachable, but the catch's PhiC names its upsilon, which Julia's
    # verifier allows. Pruning the block drops that upsilon from the PhiC; a PhiC that
    # named no other is left without operands (and the catch does not read it).
    @testset "with $(length(live)) live upsilons" for live in (Any[SSAValue(2)], Any[])
        ir = build_ir([
            (stmts=[(Core.EnterNode(4), Any)], succs=[2, 4]),
            (stmts=[(Core.UpsilonNode(Argument(2)), Int),
                    (Expr(:call, Core.throw, ErrorException("a")), Union{}),
                    (ReturnNode(), Union{})], succs=Int[]),
            (stmts=[(Core.UpsilonNode(7), Int), (ReturnNode(), Union{})], succs=Int[]),
            (stmts=[(Core.PhiCNode(Any[live..., SSAValue(5)]), Int),
                    (Expr(:pop_exception, SSAValue(1)), Nothing),
                    (ReturnNode(isempty(live) ? Argument(2) : SSAValue(7)), Any)],
             succs=Int[]),
        ], Any[Tuple{}, Int])
        ir.stmts.flag .= UInt32(0)
        CC.verify_ir(ir)
        m = ingest(ir; exceptions=:structured)
        @test length(m.blocks) == 3
        @test only(s.stmt for b in m.blocks for s in b.body if s.stmt isa Core.PhiCNode).values ==
              live
    end
end

@testset "handler stacks" begin
    m = ingest(first(only(code_ircode(eh_nested, (Int,)))); exceptions=:structured)
    stacks = handler_stacks(m)
    enter_blocks = [bid for (bid, b) in enumerate(m.blocks) if b.term isa MEnter]
    @test length(enter_blocks) == 2
    outer, inner = sort(enter_blocks; by=bid -> length(stacks[bid]))
    # The inner try is entered with the outer handler active; its body runs with both.
    @test stacks[outer] == Int[] && stacks[inner] == [m.blocks[outer].term.id]
    @test stacks[m.blocks[inner].term.body.target] ==
          [m.blocks[outer].term.id, m.blocks[inner].term.id]
    # The catch block keeps the stack its try was entered with.
    @test stacks[m.blocks[inner].term.catch_dest] == stacks[inner]
    # `return` out of two trys: Julia's one `:leave` popping both becomes a chain of
    # leave blocks, each alone in its block and popping the innermost handler.
    ir = first(only(code_ircode(eh_nested_return, (Int,))))
    @test any(s -> s isa Expr && s.head === :leave && length(s.args) == 2, ir.stmts.stmt)
    m = ingest(ir; exceptions=:structured)
    stacks = handler_stacks(m)
    nleaves = 0
    for (bid, b) in enumerate(m.blocks), s in b.body
        is_leave(s.stmt) || continue
        nleaves += 1
        @test length(b.body) == 1 && length(s.stmt.args) == 1
        @test s.stmt.args[1].id == stacks[bid][end]
    end
    @test nleaves >= 3
    # A block reached with and without a handler active is rejected.
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 3), Any)],               succs=[3, 2]),
        (stmts=[(Core.EnterNode(4), Any)],                       succs=[4, 3]),
        (stmts=[(ReturnNode(1), Any)],                           succs=Int[]),
        (stmts=[(ReturnNode(2), Any)],                           succs=Int[]),
    ], Any[Any, Bool])
    @test_throws UnstructuredControlFlowError ingest(ir; exceptions=:structured)
end

"""The MCFG `ingest` builds for `f` at `Tuple{Int}`, with try/catch."""
eh_mcfg(f) = ingest(first(only(code_ircode(f, Tuple{Int}))); exceptions=:structured)

@testset "try regions" begin
    m = eh_mcfg(eh_nested)
    regions = try_info(m)
    @test length(regions) == 2
    outer, inner = sort!(collect(values(regions)); by=r -> r.depth)
    @test outer.depth == 0 && inner.depth == 1
    # The inner try (body and handler) nests in the outer body.
    @test inner.block in outer.body
    @test issubset(inner.body, outer.body) && issubset(inner.handler, outer.body)
    @test isdisjoint(outer.body, outer.handler)
    # Every edge out of a try's body and handler lands on a block with the stack the
    # try was entered with. That includes an exit out of a try nested in a catch,
    # which pops the catch's exception before it leaves the nested try: the leave
    # block after the pop still belongs to the catch.
    @testset "$(nameof(f))" for (f, _) in EH_CASES
        m = eh_mcfg(f)
        stacks = handler_stacks(m)
        for r in values(try_info(m)), ref in try_exit_refs(m, r)
            @test stacks[edge_of(m, ref).target] == stacks[r.block]
        end
    end
    # A body that cannot complete normally: the catch dominates the loop's latch,
    # but the handler region ends at the catch's `pop_exception`.
    m = eh_mcfg(eh_throwing_body_in_loop)
    r = only(values(try_info(m)))
    loops = IRStructurizer.natural_loops_m(m)
    @test !any(h -> h in r.handler, keys(loops))
end

"""For each `pop_exception` in `m`: the handler depth of the catch it pops (its
try's entry depth), and the depth of the block it runs in."""
function eh_pop_depths(m)
    stacks = handler_stacks(m)
    enter_depth = Dict(b.term.id => length(stacks[bid]) for (bid, b) in enumerate(m.blocks)
                       if b.term isa MEnter && stacks[bid] !== nothing)
    return [(enter_depth[s.stmt.args[1].id], length(stacks[bid]))
            for (bid, b) in enumerate(m.blocks) if stacks[bid] !== nothing
            for s in b.body if is_pop_exception(s.stmt)]
end

@testset "a pop after a leave of an enclosing try moves before it" begin
    # A catch that returns out of an enclosing try: Julia leaves the outer try,
    # then pops the inner catch's exception, one handler shallower than the catch.
    # Moved before the leave, the pop runs in its catch.
    @testset "$(nameof(f))" for f in (eh_nested_return, eh_return_from_inner_catch,
                                      eh_return_from_nested_catch_in_loop, eh_three_levels)
        @test all(((d, at),) -> at >= d, eh_pop_depths(eh_mcfg(f)))
    end
end

@testset "a pop before leaving trys nested in its catch moves after them" begin
    # A `continue` out of a try nested in a catch pops the catch's exception, then
    # leaves the nested try. Moved after the leave, every pop runs at exactly the
    # handler depth of its catch.
    @testset "$(nameof(f))" for (f, _) in EH_CASES
        @test all(((d, at),) -> at == d, eh_pop_depths(eh_mcfg(f)))
    end
end

end  # exceptions
