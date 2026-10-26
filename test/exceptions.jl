#=============================================================================
 Exception handling: EnterNode / :leave / PhiC+Upsilon, lifted with
 `exceptions=:structured`.

 The shapes below are functions with try/catch. The testsets check the MCFG that
 `ingest(ir; exceptions=:structured)` and `normalize_cf!` build from them.
=============================================================================#

using IRStructurizer: ingest, handler_stacks, is_leave, MEnter

const EH_LOG = Any[]
@noinline eh_log(@nospecialize(x)) = (push!(EH_LOG, x); nothing)
"""Throw `e`, logging it first. The test functions throw through this, so a log
also records the throws that a handler catches."""
@noinline eh_throw(@nospecialize(e)) = (push!(EH_LOG, (:throw, rt_payload(e))); throw(e))
@noinline eh_g(x::Int) = x > 10 ? eh_throw(ErrorException("big")) : x + 1
@noinline eh_h(x::Int) = x < 0 ? eh_throw(DomainError(x)) : x * 2

#----------------------------------------------------------------------------- shapes

eh_basic(x) = try eh_g(x) catch; -1 end
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

end  # exceptions
