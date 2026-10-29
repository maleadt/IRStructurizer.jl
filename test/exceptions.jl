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
# A catch returns out of a try nested in another catch, itself in a try body: the
# return leaves two trys and pops two catches' exceptions at once.
function eh_return_across_catches_and_trys(x)
    try
        try
            eh_log(10)
            x > 5 && eh_throw(ErrorException("a"))
        catch
            try
                try
                    eh_throw(ErrorException("b"))
                catch
                    eh_log(0)
                    return x
                end
            catch
                rethrow()
            end
        end
    catch
    end
    -x
end
# A catch that either runs a try of its own or not, both paths joining at a block
# that pops the outer catch. The inner path reaches the join holding two
# exceptions, the other path one. `inner_first` puts the inner path on the
# branch's first edge, so the state analysis reaches the join through it first.
function eh_split_join_ir(inner_first::Bool)
    thr = (Expr(:call, Core.throw, ErrorException("a")), Union{})
    unreachable = (ReturnNode(), Union{})
    # %1 = enter (outer); %6 = enter (inner); the join pops %1.
    D, I, J = inner_first ? (8, 4, 7) : (4, 5, 8)
    blocks = Vector{Any}(undef, 9)
    blocks[1] = (stmts=[(Core.EnterNode(3), Any)], succs=[3, 2])
    blocks[2] = (stmts=[thr, unreachable], succs=Int[])
    blocks[3] = (stmts=[(GotoIfNot(Core.Argument(2), inner_first ? D : I), Any)],
                 succs=inner_first ? [I, D] : [D, I])
    blocks[D] = (stmts=[(GotoNode(J), Any)], succs=[J])
    blocks[I] = (stmts=[(Core.EnterNode(I + 2), Any)], succs=[I + 2, I + 1])
    blocks[I+1] = (stmts=[thr, unreachable], succs=Int[])
    blocks[I+2] = (stmts=[(GotoNode(J), Any)], succs=[J])
    blocks[J] = (stmts=[(Expr(:pop_exception, SSAValue(1)), Nothing), (GotoNode(9), Any)],
                 succs=[9])
    blocks[9] = (stmts=[(ReturnNode(Core.Argument(2)), Any)], succs=Int[])
    return build_ir(blocks, Any[Tuple{}, Bool])
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

# A `break` from a try in a catch nested in another catch pops both exceptions,
# then leaves the try. Split into one pop per catch, both pops move past the leave.
function eh_break_from_try_in_nested_catches(x)
    for i in 1:3
        try
            x > 0 && eh_throw(ErrorException("a"))
        catch
            try
                x > 1 && eh_throw(ErrorException("b"))
            catch
                try
                    x > 2 && break
                    eh_log(1)
                catch
                end
            end
        end
        eh_log(i)
    end
    x
end

# The same with a try around the middle catch: a `break` from the innermost catch
# pops three catches' exceptions and leaves two trys (`pop A; leave Y; leave X`).
# The middle pop has to pass one leave, the outer pop both.
function eh_break_from_catch_in_trys_in_catches(x)
    for i in 1:3
        try
            x > 0 && eh_throw(ErrorException("a"))
        catch
            try
                try
                    x > 1 && eh_throw(ErrorException("b"))
                catch
                    try
                        try
                            x > 2 && eh_throw(ErrorException("c"))
                        catch
                            x > 3 && break
                            eh_log(3)
                        end
                        eh_log(4)
                    catch
                    end
                end
                eh_log(5)
            catch
            end
        end
        eh_log(i)
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
    (eh_return_across_catches_and_trys, (1, 7)),
    (eh_break_from_try_in_nested_catches, (0, 1, 2, 5)),
    (eh_break_from_catch_in_trys_in_catches, (0, 1, 2, 3, 5)),
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

"""Every exception stack each block of `m` can be entered with, as the enters whose
exceptions are on it, outermost first. A catch edge pushes its enter onto the stack
the enter ran with, and `pop_exception %x` cuts the stack back to below `x` (or
leaves it alone if `x` is not on it). Unlike `exception_states`, this keeps every
stack that reaches a join. A stack that holds a catch twice is dropped: Julia 1.11
leaks the exception of a `finally` that exits after a throw, and in a loop such
stacks would grow without end."""
function eh_incoming_stacks(m)
    stacks = [Set{Vector{Int}}() for _ in m.blocks]
    push!(stacks[m.entry], Int[])
    work = [m.entry]
    while !isempty(work)
        b = pop!(work)
        blk = m.blocks[b]
        for s0 in collect(stacks[b])
            s = copy(s0)
            for st in blk.body
                is_pop_exception(st.stmt) || continue
                k = findfirst(==(st.stmt.args[1].id), s)
                k === nothing || resize!(s, k - 1)
            end
            t = blk.term
            for tgt in IRStructurizer._term_targets(t)
                s′ = t isa MEnter && tgt == t.catch_dest ? vcat(s, t.id) : s
                (allunique(s′) && !(s′ in stacks[tgt])) || continue
                push!(stacks[tgt], s′)
                push!(work, tgt)
            end
        end
    end
    return stacks
end

@testset "a pop that leaves several catches is split, one per catch" begin
    # A `break` from a catch nested in another catch pops straight to the outer
    # state. Split, every pop on a path to a continuation pops one exception:
    # on every stack that reaches it, its catch's exception is the innermost one
    # (or it is not there, and the pop does nothing). A `return` may still pop
    # several catches at once: it has no continuation. Each pop also comes after
    # its enter.
    @testset "$(nameof(f))" for (f, _) in EH_CASES
        m = eh_mcfg(f)
        domtree = CC.construct_domtree(IRStructurizer.build_cfg(m))
        enter_block = Dict(b.term.id => bid for (bid, b) in enumerate(m.blocks)
                           if b.term isa MEnter)
        for (bid, b) in enumerate(m.blocks), st in b.body
            is_pop_exception(st.stmt) || continue
            x = st.stmt.args[1].id
            @test bid != enter_block[x] && CC.dominates(domtree, enter_block[x], bid)
        end
        for (bid, ins) in enumerate(eh_incoming_stacks(m))
            b = m.blocks[bid]
            b.term isa IRStructurizer.MReturn && continue
            for s0 in ins
                s = copy(s0)
                for st in b.body
                    is_pop_exception(st.stmt) || continue
                    x = st.stmt.args[1].id
                    k = findfirst(==(x), s)
                    @test k === nothing || k == length(s)
                    k === nothing || resize!(s, k - 1)
                end
            end
        end
    end
    @testset "a pop is split only where its catches' enters dominate it" begin
        @testset "inner_first=$inner_first" for inner_first in (false, true)
            ir = eh_split_join_ir(inner_first)
            m = ingest(ir; exceptions=:structured)
            domtree = CC.construct_domtree(IRStructurizer.build_cfg(m))
            enter_block = Dict(b.term.id => bid for (bid, b) in enumerate(m.blocks)
                               if b.term isa MEnter)
            pops = [(st.stmt.args[1].id, bid) for (bid, b) in enumerate(m.blocks)
                    for st in b.body if is_pop_exception(st.stmt)]
            @test length(pops) == 1 && first(only(pops)) == 1
            dominated = all(((x, bid),) -> CC.dominates(domtree, enter_block[x], bid), pops)
            @test dominated
        end
    end
end

"""The edge operands and upsilon values that `ingest(ir; exceptions=:structured)` leaves
naming a `Union{}`-typed phi or PhiC (of `ir`, or of the MCFG), or a value that no
longer exists (a block argument, statement or enter of the MCFG)."""
function eh_bottom_refs(ir)
    m = ingest(ir; exceptions=:structured)
    bottom = Set{Int}(i for (i, (s, t)) in enumerate(zip(ir.stmts.stmt, ir.stmts.type))
                      if t === Union{} && s isa Union{PhiNode, Core.PhiCNode})
    defined = Set{Int}()
    for b in m.blocks
        union!(bottom, (a for a in b.args if get(m.types, a, Any) === Union{}))
        union!(bottom, (s.id for s in b.body if s.stmt isa Core.PhiCNode && s.type === Union{}))
        union!(defined, b.args, (s.id for s in b.body))
        b.term isa MEnter && push!(defined, b.term.id)
    end
    bad(v) = v isa SSAValue && (v.id in bottom || !(v.id in defined))
    refs = Any[]
    for b in m.blocks
        t = b.term
        edges = t isa IRStructurizer.MGoto ? (t.edge,) :
                t isa IRStructurizer.MCondBr ? (t.t, t.f) : t isa MEnter ? (t.body,) : ()
        foreach(e -> append!(refs, filter(bad, e.args)), edges)
        for s in b.body
            s.stmt isa Core.UpsilonNode && isdefined(s.stmt, :val) && bad(s.stmt.val) &&
                push!(refs, s.stmt.val)
        end
    end
    return refs
end

@testset "values undefined on the catch path become Undef" begin
    # A variable never assigned before a throw reaches the catch through a
    # `Union{}`-typed `PhiCNode`, and phis carry it on. Nothing reads such a value
    # (Julia guards it with `throw_undef_if_not`), so no edge operand or upsilon
    # names one after ingest, nor a block argument that ingest dropped.
    @testset "$(nameof(f))" for (f, _) in EH_CASES
        @test isempty(eh_bottom_refs(first(only(code_ircode(f, Tuple{Int})))))
    end
    # Catch 1's `Union{}` PhiC reaches the body of a second try on its enter's edge,
    # into two phis: a `Union{}` one, which an upsilon takes on to catch 2, and an
    # `Any` one. The `Union{}` phi goes, and the `Any` one gets `Undef`.
    thr = (Expr(:call, Core.throw, ErrorException("a")), Union{})
    ir = build_ir([
        (stmts=[(Core.EnterNode(3), Any)], succs=[2, 3]),
        (stmts=[(Core.UpsilonNode(), Union{}), thr, (ReturnNode(), Union{})], succs=Int[]),
        (stmts=[(Core.PhiCNode(Any[SSAValue(2)]), Union{}), (Core.EnterNode(5), Any)],
         succs=[4, 5]),
        (stmts=[(PhiNode(Int32[3], Any[SSAValue(5)]), Union{}),
                (PhiNode(Int32[3], Any[SSAValue(5)]), Any),
                (Core.UpsilonNode(SSAValue(7)), Union{}), thr, (ReturnNode(), Union{})],
         succs=Int[]),
        (stmts=[(Core.PhiCNode(Any[SSAValue(9)]), Union{}),
                (Expr(:pop_exception, SSAValue(6)), Nothing), (GotoNode(6), Any)], succs=[6]),
        (stmts=[(Expr(:pop_exception, SSAValue(1)), Nothing),
                (ReturnNode(Argument(2)), Any)], succs=Int[]),
    ], Any[Tuple{}, Int])
    ir.stmts.flag .= UInt32(0)
    CC.verify_ir(ir)
    @test isempty(eh_bottom_refs(ir))
    m = ingest(ir; exceptions=:structured)
    @test [a for b in m.blocks for a in b.args] == [8]
    @test only(b.term.body.args for b in m.blocks if b.term isa MEnter && b.term.id == 6) ==
          Any[IRStructurizer.Undef(Any)]
    # Some of the cases do carry such values: Julia's IR for them has `Union{}`-typed
    # phis, PhiCs or upsilons before the rewrite.
    @testset "$(nameof(f)) carries Union{} values" for f in (eh_finally_return,
                                                              eh_return_from_try_in_catch)
        ir = first(only(code_ircode(f, (Int,))))
        @test any(((s, t),) -> t === Union{} &&
                  (s isa Core.PhiCNode || s isa PhiNode || s isa Core.UpsilonNode),
                  zip(ir.stmts.stmt, ir.stmts.type))
    end
end

end  # exceptions
