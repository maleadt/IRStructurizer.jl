#=============================================================================
 The structurizer's standing regression net.

 One @testset per CFG family, plus three divergence CFGs built as synthetic IR
 with structural assertions. Every entry is an executable roundtrip
 (structurize → unstructurize → execute == direct) unless it is a pure
 structural assertion.

 Generative exec-vs-direct fuzzing is intentionally NOT here — it lives in the
 untracked development scripts (e.g. `m4_loopfuzz.jl`). The test suite stays
 deterministic; fuzzing is a development tool, run by hand.

 The synthetic-IR builder pins exact CFG shapes that natural Julia source can't
 reliably produce, so we can assert on the structure directly (the chosen merge,
 the body emitted once), not only through execution.
=============================================================================#

# Bindings named like the intrinsics loop promotion recognizes.
module AliasedIntrinsics
const slt_int = Core.Intrinsics.sle_int   # an inclusive bound under an exclusive name
const plus = Core.Intrinsics.add_int
function misnamed(n::Int)
    i = s = 0
    while slt_int(i, n)
        s += 1
        i += 1
    end
    return s
end
function renamed(n::Int)
    i = s = 0
    while Core.Intrinsics.slt_int(i, n)
        s = plus(s, i)
        i = plus(i, 1)
    end
    return s
end
end

# A constant the tests rebind after inferring code that calls it.
module ReboundIntrinsic
const cmp = Core.Intrinsics.slt_int
function counted(n::Int)
    i = s = 0
    while cmp(i, n)
        s += 1
        i += 1
    end
    return s
end
end

@testset "regression suite" begin

#=============================================================================
 Divergence CFGs — structural assertions
=============================================================================#

@testset "successor that is also a merge" begin
    # E→{T,F}, F→T, T→X.  T has two predecessors (E and F), so by edge-domination
    # T's branch region is EMPTY and T is the continuation — not pulled into the
    # then-region (which block-domination would do). A φ at T gives cond ? 10 : 20.
    function q1_ir()
        build_ir([
            (stmts=[(GotoIfNot(Argument(2), 3), Any)], succs=[3, 2]),     # E: false→F, true→T
            (stmts=[(PhiNode(Int32[1, 3], Any[10, 20]), Int),             # T: φ(E=>10, F=>20)
                    (GotoNode(4), Any)],               succs=[4]),         # T→X
            (stmts=[(GotoNode(2), Any)],               succs=[2]),         # F→T
            (stmts=[(ReturnNode(SSAValue(2)), Any)],   succs=Int[]),       # X: return φ
        ], Any[Any, Bool])
    end

    ir = q1_ir()
    domtree = Core.Compiler.construct_domtree(ir)
    region = Set(1:length(ir.cfg.blocks))
    then_blocks, else_blocks, merge =
        IRStructurizer.find_branch_regions(ir.cfg, domtree, 1, 2, 3, region)  # E: true=BB2, false=BB3
    @test merge == 2                       # T is the continuation
    @test !(2 in then_blocks)              # ...not swallowed into an arm
    @test !(2 in else_blocks)
    @test isempty(then_blocks)             # T's branch region is empty (2 preds)

    sci = StructuredIRCode(q1_ir())
    @test execute(sci, true) == 10
    @test execute(sci, false) == 20
end

@testset "virtual exit, continuation by exclusion (two layouts)" begin
    # E→{T,F}, T→M, F→{M,R}, R:return, M→X.  ipdom(E) is the virtual exit (F
    # reaches R without M), yet the continuation is unambiguously M. A φ at M
    # gives cond ? 100 : (c2 ? 200 : 999). Built in two block layouts to assert
    # the merge is M regardless of numbering (layout independence).
    function q2_ir(; m_first::Bool)
        if !m_first
            blocks = [  # BB1=E BB2=T BB3=F BB4=M BB5=R BB6=X
                (stmts=[(GotoIfNot(Argument(2), 3), Any)], succs=[3, 2]),
                (stmts=[(GotoNode(4), Any)],               succs=[4]),
                (stmts=[(GotoIfNot(Argument(3), 5), Any)], succs=[5, 4]),
                (stmts=[(PhiNode(Int32[2, 3], Any[100, 200]), Int),
                        (GotoNode(6), Any)],               succs=[6]),
                (stmts=[(ReturnNode(999), Any)],           succs=Int[]),
                (stmts=[(ReturnNode(SSAValue(4)), Any)],   succs=Int[]),
            ]
            return build_ir(blocks, Any[Any, Bool, Bool]), 4   # M is BB4
        else
            blocks = [  # BB1=E BB2=T BB3=M BB4=X BB5=F BB6=R
                (stmts=[(GotoIfNot(Argument(2), 5), Any)], succs=[5, 2]),
                (stmts=[(GotoNode(3), Any)],               succs=[3]),
                (stmts=[(PhiNode(Int32[2, 5], Any[100, 200]), Int),
                        (GotoNode(4), Any)],               succs=[4]),
                (stmts=[(ReturnNode(SSAValue(3)), Any)],   succs=Int[]),
                (stmts=[(GotoIfNot(Argument(3), 6), Any)], succs=[6, 3]),
                (stmts=[(ReturnNode(999), Any)],           succs=Int[]),
            ]
            return build_ir(blocks, Any[Any, Bool, Bool]), 3   # M is BB3
        end
    end

    for m_first in (false, true)
        ir, m_bb = q2_ir(; m_first)
        domtree = Core.Compiler.construct_domtree(ir)
        region = Set(1:length(ir.cfg.blocks))
        fdest = (ir.stmts.stmt[ir.cfg.blocks[1].stmts[end]]::GotoIfNot).dest
        _, _, merge = IRStructurizer.find_branch_regions(ir.cfg, domtree, 1, 2, fdest, region)
        @test merge == m_bb                # M chosen regardless of its index

        sci = StructuredIRCode(q2_ir(; m_first)[1])
        @test execute(sci, true,  true)  == 100   # cond
        @test execute(sci, false, true)  == 200   # !cond, c2
        @test execute(sci, false, false) == 999   # !cond, !c2 → R
    end
end

@testset "a continuation that one arm of its branch would absorb" begin
    # `x > 1 && error(..)` has one arm that throws, so every edge into its
    # continuation leaves the other arm. Muxed at that branch, the mux joined the
    # arm, and the next round found the same two entries (the `break` and the
    # fall-through), without end. The loop's exit dispatch, which dominates the
    # branch and joins those paths with the `x > 8` arm's, has to be muxed first.
    function cont_absorbed(x)
        w = 0
        while w < 3
            w += 1
            if x > 8
                x > 9 && continue
            else
                x > 1 && error("absorbed")
                x > -2 && break
            end
            break
        end
        10x + w             # which path ran
    end
    sci, _ = code_structured(cont_absorbed, Tuple{Int}) |> only     # validates
    for x in (-5, -2, 0, 1, 9, 10, 12)
        @test execute(sci, x) == cont_absorbed(x)
    end
    @test_throws ErrorException execute(sci, 5)
end

@testset "short-circuit || body emitted once" begin
    # `if a || b { body }` — body is the multi-entry continuation reached from
    # both arms. The edge multiplexer emits it exactly once (no tail duplication).
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    function or_body!(r::Base.RefValue{Int}, a::Bool, b::Bool)
        if opaque(a) || opaque(b)
            r[] = 99
        end
        return nothing
    end
    sci, _ = code_structured(or_body!, Tuple{Base.RefValue{Int}, Bool, Bool}) |> only
    @test count_stmts(sci.entry, s -> iscall_to(s, :setfield!)) == 1   # once, not twice
    for (a, b) in ((false, false), (false, true), (true, false), (true, true))
        r = Ref(0); execute(sci, r, a, b)
        @test r[] == ((a || b) ? 99 : 0)
    end
end

@testset "short-circuit arms merging beside a fall-through edge" begin
    # `if a; A elseif b || c || d; B else; C end` inlined into a user of the
    # result. The merge has three predecessors: the `if a` arm, the `||` chain's
    # own merge (all yielding B), and the fall-through edge that yields C. Once
    # dropped the C edge, leaving B unconditional.
    @inline function pick(x::Float64, y::Float64)
        if x > 1.0 && y > 1.0
            return 1.0
        elseif x < 0.0 || y < 0.0 || y > 10.0
            return -99.0
        else
            return x
        end
    end
    use_pick(x::Float64, y::Float64) = copysign(pick(x, y), y)
    for args in ((2.0, 2.0), (-1.0, 1.0), (0.5, 0.5), (0.5, -1.0), (0.5, 20.0), (0.0, 1.0))
        @test @roundtrip use_pick(args...)
    end
end

@testset "single-predecessor phi with no value" begin
    # The copy of an undefined operand is an `Undef` statement, which has to lower
    # back to an empty phi rather than to the `Undef` object.
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 3), Any)],                       succs=[2, 3]),
        (stmts=[(PhiNode(Int32[], Any[]), Float64),
                (Expr(:call, GlobalRef(Core, :ifelse), true, Argument(3), SSAValue(2)), Float64),
                (ReturnNode(SSAValue(3)), Any)],                         succs=Int[]),
        (stmts=[(ReturnNode(1.0), Any)],                                 succs=Int[]),
    ], Any[Any, Bool, Float64])
    sci = StructuredIRCode(ir)
    ir2 = CC.IRCode(sci)
    CC.verify_ir(ir2)
    @test !any(s -> s isa Undef, ir2.stmts.stmt)
    @test any(s -> s isa PhiNode && isempty(s.edges), ir2.stmts.stmt)
    @test execute(sci, true, 0.5) === 0.5
    @test execute(sci, false, 0.5) === 1.0
end

@testset "block argument with no incoming value" begin
    # Optimized IR can keep a phi with no incoming values (`φ()`), e.g. a union-split
    # result that only the other member's path computes, as long as a later phi or
    # a statement still names it. Its block argument is `Undef` on every edge but is
    # still a value its uses refer to.
    mul = GlobalRef(Core.Intrinsics, :mul_float)
    add = GlobalRef(Core.Intrinsics, :add_int)
    slt = GlobalRef(Core.Intrinsics, :slt_int)
    ifelse = GlobalRef(Core, :ifelse)

    # Read by a later phi, on an edge whose value is never used.
    #  1: goto 5 if not c      2: goto 4 if not d      3: goto 4
    #  4: %4 = φ()                                      goto 6
    #  5: %6 = x * x                                    goto 6
    #  6: %8 = φ(4 => %4, 5 => %6); %9 = φ(4 => false, 5 => true); return ifelse(%9, %8, 1.0)
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 5), Any)],                      succs=[5, 2]),
        (stmts=[(GotoIfNot(Argument(3), 4), Any)],                      succs=[4, 3]),
        (stmts=[(GotoNode(4), Any)],                                    succs=[4]),
        (stmts=[(PhiNode(Int32[], Any[]), Float64), (GotoNode(6), Any)], succs=[6]),
        (stmts=[(Expr(:call, mul, Argument(4), Argument(4)), Float64),
                (GotoNode(6), Any)],                                    succs=[6]),
        (stmts=[(PhiNode(Int32[4, 5], Any[SSAValue(4), SSAValue(6)]), Float64),
                (PhiNode(Int32[4, 5], Any[false, true]), Bool),
                (Expr(:call, ifelse, SSAValue(9), SSAValue(8), 1.0), Float64),
                (ReturnNode(SSAValue(10)), Any)],                       succs=Int[]),
    ], Any[Any, Bool, Bool, Float64])
    sci = StructuredIRCode(ir)
    for c in (true, false), d in (true, false)
        @test execute(sci, c, d, 0.75) === (c ? 1.0 : 0.75 * 0.75)
    end

    # The same through a chain of phis.
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 6), Any)],                      succs=[6, 2]),
        (stmts=[(GotoIfNot(Argument(3), 4), Any)],                      succs=[4, 3]),
        (stmts=[(GotoNode(4), Any)],                                    succs=[4]),
        (stmts=[(PhiNode(Int32[], Any[]), Float64), (GotoNode(5), Any)], succs=[5]),
        (stmts=[(PhiNode(Int32[4], Any[SSAValue(4)]), Float64),
                (GotoNode(7), Any)],                                    succs=[7]),
        (stmts=[(Expr(:call, mul, Argument(4), Argument(4)), Float64),
                (GotoNode(7), Any)],                                    succs=[7]),
        (stmts=[(PhiNode(Int32[5, 6], Any[SSAValue(6), SSAValue(8)]), Float64),
                (PhiNode(Int32[5, 6], Any[false, true]), Bool),
                (Expr(:call, ifelse, SSAValue(11), SSAValue(10), 1.0), Float64),
                (ReturnNode(SSAValue(12)), Any)],                       succs=Int[]),
    ], Any[Any, Bool, Bool, Float64])
    sci = StructuredIRCode(ir)
    for c in (true, false), d in (true, false)
        @test execute(sci, c, d, 0.75) === (c ? 1.0 : 0.75 * 0.75)
    end

    # Read by a statement at a branch merge.
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 3), Any)],                      succs=[3, 2]),
        (stmts=[(GotoNode(3), Any)],                                    succs=[3]),
        (stmts=[(PhiNode(Int32[], Any[]), Float64),
                (Expr(:call, ifelse, true, Argument(3), SSAValue(3)), Float64),
                (ReturnNode(SSAValue(4)), Any)],                        succs=Int[]),
    ], Any[Any, Bool, Float64])
    sci = StructuredIRCode(ir)
    @test execute(sci, true, 0.75) === 0.75
    @test execute(sci, false, 0.75) === 0.75

    # At a loop header, read by a statement in the body. `%2` has no value on
    # either edge, `%3` none on entry.
    #  1: goto 2
    #  2: %2 = φ(); %3 = φ(4 => %6); %4 = φ(1 => 0, 4 => %6)
    #     %5 = ifelse(true, x, %2)                   goto 3
    #  3: %6 = %4 + 1; %7 = %6 < 3                   goto 5 if not %7
    #  4: goto 2
    #  5: return (%5, ifelse(true, 7, %3))
    ir = build_ir([
        (stmts=[(GotoNode(2), Any)],                                    succs=[2]),
        (stmts=[(PhiNode(Int32[], Any[]), Float64),
                (PhiNode(Int32[4], Any[SSAValue(6)]), Int),
                (PhiNode(Int32[1, 4], Any[0, SSAValue(6)]), Int),
                (Expr(:call, ifelse, true, Argument(2), SSAValue(2)), Float64)], succs=[3]),
        (stmts=[(Expr(:call, add, SSAValue(4), 1), Int),
                (Expr(:call, slt, SSAValue(6), 3), Bool),
                (GotoIfNot(SSAValue(7), 5), Any)],                      succs=[4, 5]),
        (stmts=[(GotoNode(2), Any)],                                    succs=[2]),
        (stmts=[(Expr(:call, ifelse, true, 7, SSAValue(3)), Int),
                (Expr(:call, Core.tuple, SSAValue(5), SSAValue(10)), Tuple{Float64, Int}),
                (ReturnNode(SSAValue(11)), Any)],                       succs=Int[]),
    ], Any[Any, Float64])
    sci = StructuredIRCode(ir)
    @test execute(sci, 0.75) === (0.75, 7)
end

@testset "loop carry of a literal `nothing`" begin
    ir = build_ir([
        (stmts=[(GotoNode(2), Any)],                                    succs=[2]),
        (stmts=[(PhiNode(Int32[1, 4], Any[nothing, nothing]), Nothing),
                (PhiNode(Int32[1, 4], Any[0, SSAValue(4)]), Int)],      succs=[3]),
        (stmts=[(Expr(:call, GlobalRef(Core.Intrinsics, :add_int), SSAValue(3), 1), Int),
                (Expr(:call, GlobalRef(Core.Intrinsics, :slt_int), SSAValue(4), 3), Bool),
                (GotoIfNot(SSAValue(5), 5), Any)],                      succs=[4, 5]),
        (stmts=[(GotoNode(2), Any)],                                    succs=[2]),
        (stmts=[(ReturnNode(SSAValue(2)), Any)],                        succs=Int[]),
    ], Any[Any])
    @test execute(StructuredIRCode(ir)) === nothing
end

@testset "phi operand is a GlobalRef" begin
    # A merge can carry a `GlobalRef` to a const binding as an operand (Base's
    # math kernels yield `Inf` that way). Typing the operand as the GlobalRef
    # object rather than the binding's value failed block-arg validation.
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 3), Any)],                     succs=[3, 2]),
        (stmts=[(GotoNode(4), Any)],                                   succs=[4]),
        (stmts=[(GotoNode(4), Any)],                                   succs=[4]),
        (stmts=[(PhiNode(Int32[2, 3], Any[GlobalRef(Base, :Inf), 0.0]), Float64),
                (ReturnNode(SSAValue(4)), Any)],                       succs=Int[]),
    ], Any[Any, Bool])
    sci = StructuredIRCode(ir)
    @test execute(sci, true) === Inf
    @test execute(sci, false) === 0.0
end

@testset "unreachable blocks" begin
    # i = 0; while (i += 1) < n; end; return i, plus dead blocks: BB4 feeds the
    # loop header a value it defines, BB6 is a dead cycle.
    ir = build_ir([
        (stmts=[(GotoNode(2), Any)], succs=[2]),
        (stmts=[(PhiNode(Int32[1, 3, 4], Any[0, SSAValue(3), SSAValue(7)]), Int),
                (Expr(:call, GlobalRef(Base, :add_int), SSAValue(2), 1), Int),
                (Expr(:call, GlobalRef(Base, :slt_int), SSAValue(3), Argument(2)), Bool),
                (GotoIfNot(SSAValue(4), 5), Any)], succs=[5, 3]),
        (stmts=[(GotoNode(2), Any)], succs=[2]),
        (stmts=[(Expr(:call, GlobalRef(Base, :add_int), Argument(2), 1), Int),
                (GotoNode(2), Any)], succs=[2]),
        (stmts=[(ReturnNode(SSAValue(3)), Any)], succs=Int[]),
        (stmts=[(GotoNode(6), Any)], succs=[6]),
    ], Any[Any, Int])
    @test length(IRStructurizer.ingest(ir).blocks) == 4
    sci = StructuredIRCode(ir)
    for n in (0, 1, 5)
        @test execute(sci, n) == max(n, 1)
    end
end

@testset "an edge operand wider than its phi is narrowed" begin
    # Julia types a phi by what inference knows on each edge: `x::Any` reaching it
    # from behind `x isa Int` feeds an `Int` phi. The structurizer narrows such an
    # operand with a PiNode in the region that takes the edge; without it the
    # validator rejects the op's operand.
    function narrow_decl(x)
        x::Int = x
        x + 1
    end
    sci, _ = code_structured(narrow_decl, Tuple{Any}) |> only   # validates
    for x in (1, 7)
        @test execute(sci, x) == narrow_decl(x)
    end
    @test_throws MethodError execute(sci, "a")
    # Union-split code (#69): `convert(Int, ⋯)` on the `Int` arm of the split
    # inlines to the identity, so no π marks that the `Union{Float64, Int}` value
    # reaching `k`'s `Int` phi on that edge is the literal `1`. The edge is narrowed
    # by a correlated `Bool` phi, not by an `isa` branch.
    union_split_decl(m::Float64, c::Bool) = (k::Int = c ? m : 1; k)
    sci, _ = code_structured(union_split_decl, Tuple{Float64, Bool}) |> only   # validates
    for (m, c) in ((2.0, true), (-3.0, true), (1.5, false))
        @test execute(sci, m, c) === union_split_decl(m, c)
    end
    @test_throws InexactError execute(sci, 2.5, true)
    # The same refinement after an inlined `iterate` (a `Union{Nothing, Tuple}` value
    # feeding a `Tuple` phi), before the optimizer has removed it.
    function narrow_iter(n)
        a = Tuple{Int,Int}[]
        for i in 1:n
            for j in 3:4
                push!(a, (i, j))
                j == 6 && break
            end
        end
        a
    end
    ir, _ = only(code_ircode(narrow_iter, Tuple{Int}; optimize_until=3))
    sci = StructuredIRCode(ir)                                    # validates
    @test execute(sci, 3) == narrow_iter(3)
    # A single-predecessor phi narrower than its operand (%4 of %1): the walk binds
    # it with a PiNode rather than renaming it to the wider %1.
    ir = build_ir([
        (stmts=[(Expr(:call, GlobalRef(Base, :identity), Argument(2)), Any),
                (Expr(:call, GlobalRef(Core, :isa), SSAValue(1), Int), Bool),
                (GotoIfNot(SSAValue(2), 3), Any)],                     succs=[2, 3]),
        (stmts=[(PhiNode(Int32[1], Any[SSAValue(1)]), Int),
                (GotoNode(4), Any)],                                   succs=[4]),
        (stmts=[(GotoNode(4), Any)],                                   succs=[4]),
        (stmts=[(PhiNode(Int32[2, 3], Any[SSAValue(4), 0]), Int),
                (ReturnNode(SSAValue(7)), Any)],                       succs=Int[]),
    ], Any[Any, Any])
    sci = StructuredIRCode(ir)                                    # validates
    @test any(b -> any(((_, e),) -> e.stmt isa PiNode, b.body), IRStructurizer.eachblock(sci))
    @test execute(sci, 5) === 5
    @test execute(sci, "a") === 0
    # A loop init (%4 of %1, entered only if `%1 isa Int`).
    ir = build_ir([
        (stmts=[(Expr(:call, GlobalRef(Base, :identity), Argument(2)), Any),
                (Expr(:call, GlobalRef(Core, :isa), SSAValue(1), Int), Bool),
                (GotoIfNot(SSAValue(2), 4), Any)],                     succs=[2, 4]),
        (stmts=[(PhiNode(Int32[1, 3], Any[SSAValue(1), SSAValue(7)]), Int),
                (Expr(:call, GlobalRef(Base, :slt_int), SSAValue(4), 3), Bool),
                (GotoIfNot(SSAValue(5), 4), Any)],                     succs=[3, 4]),
        (stmts=[(Expr(:call, GlobalRef(Base, :add_int), SSAValue(4), 1), Int),
                (GotoNode(2), Any)],                                   succs=[2]),
        (stmts=[(PhiNode(Int32[1, 2], Any[0, SSAValue(4)]), Int),
                (ReturnNode(SSAValue(9)), Any)],                       succs=Int[]),
    ], Any[Any, Any])
    sci = StructuredIRCode(ir)                                    # validates
    @test execute(sci, 1) === 3
    @test execute(sci, 5) === 5
    @test execute(sci, "a") === 0
    # A loop carry (%3 of %1, which repeats only if `%1 isa Int`).
    ir = build_ir([
        (stmts=[(Expr(:call, GlobalRef(Base, :identity), Argument(2)), Any),
                (GotoNode(2), Any)],                                   succs=[2]),
        (stmts=[(PhiNode(Int32[1, 3], Any[0, SSAValue(1)]), Int),
                (PhiNode(Int32[1, 3], Any[0, SSAValue(9)]), Int),
                (Expr(:call, GlobalRef(Core, :isa), SSAValue(1), Int), Bool),
                (Expr(:call, GlobalRef(Base, :slt_int), SSAValue(4), 3), Bool),
                (Expr(:call, GlobalRef(Base, :and_int), SSAValue(5), SSAValue(6)), Bool),
                (GotoIfNot(SSAValue(7), 4), Any)],                     succs=[3, 4]),
        (stmts=[(Expr(:call, GlobalRef(Base, :add_int), SSAValue(4), 1), Int),
                (GotoNode(2), Any)],                                   succs=[2]),
        (stmts=[(ReturnNode(SSAValue(3)), Any)],                       succs=Int[]),
    ], Any[Any, Any])
    for promote in (false, true)
        sci = StructuredIRCode(ir; promote)                       # validates
        @test execute(sci, 5) === 5
        @test execute(sci, "a") === 0
    end
end

if isdefined(Core, :getglobal_partition)
@testset "phi operand is a binding partition" begin
    # Julia 1.14 replaces the `GlobalRef` above with the binding partition the
    # optimizer resolved it to; its type is the binding's, not the partition's.
    inf = Base.lookup_binding_partition(Base.get_world_counter(), GlobalRef(Base, :Inf))
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 3), Any)],                     succs=[3, 2]),
        (stmts=[(GotoNode(4), Any)],                                   succs=[4]),
        (stmts=[(GotoNode(4), Any)],                                   succs=[4]),
        (stmts=[(PhiNode(Int32[2, 3], Any[inf, 0.0]), Float64),
                (ReturnNode(SSAValue(4)), Any)],                       succs=Int[]),
    ], Any[Any, Bool])
    sci = StructuredIRCode(ir)
    @test execute(sci, true) === Inf
    @test execute(sci, false) === 0.0
    @test execute(copy(sci), true) === Inf
end

@testset "copy shares invoked code and partitions held as constants" begin
    sci, _ = only(code_structured(holds_partition, Tuple{Int}))
    c = copy(sci)
    @test sci.entry.parent === sci && c.entry.parent === c
    @test execute(c, 1) === (COPY_PARTITION, 1)
end

@testset "copy shares partitions beyond an array's length" begin
    # `deepcopy` copies an array's whole backing memory.
    mem = Memory{Any}(undef, 2)
    mem[1] = 1
    mem[2] = COPY_PARTITION
    block = Block()
    push!(block.body, (1, QuoteNode(Base.wrap(Array, mem, 1)), Any))
    sci = StructuredIRCode(Any[], Any[], block, 1)
    @test copy(sci).entry.body.stmts[1].value[1] == 1
end
end

#=============================================================================
 CFG families — executable roundtrip net
=============================================================================#

@testset "baseline: diamond / ternary" begin
    @test @roundtrip (x -> x > 0 ? x + 1 : x - 1)(5)
    @test @roundtrip (x -> x > 0 ? x + 1 : x - 1)(-3)
    @test @roundtrip (x -> x > 0 ? x : -x)(7)
end

@testset "short-circuit && / || and shared tail" begin
    f_or  = (x::Int, y::Int) -> (r = 0; if x > 0 || y > 0; r = 1; end; r)
    f_and = (x::Int, y::Int) -> (r = 0; if x > 0 && y > 0; r = 1; end; r)
    for (x, y) in ((1, -1), (-1, 1), (-1, -1), (1, 1))
        @test @roundtrip f_or(x, y)
        @test @roundtrip f_and(x, y)
    end
    # nested short-circuit with a shared value-producing tail
    f_nest = (x, y, z) -> (a = (x > 0 && y > 0) ? x * y : (z > 0 ? z + 1 : -z); a + 100)
    for args in ((1,1,1), (-1,1,1), (1,-1,1), (-1,-1,-1), (1,-1,-1))
        @test @roundtrip f_nest(args...)
    end
end

@testset "gated body with in-body region-exits and a loop-carried value" begin
    # Regression (silent miscompile): a `||`-guarded body inside a loop whose body
    # both (a) contains bounds-check throws — region-exits that dead-end OUT of the
    # loop, so they aren't in the loop block set — and (b) produces a value folded
    # into a loop-carried accumulator. The body must be emitted once, with the
    # accumulator threaded out — not dropped on the diverge path.
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    function gated_loop_acc(c::Bool, v::Vector{Int}, n::Int)
        s = 0
        for k in 1:n
            if opaque(c) || k > 2
                s += (k == 1) ? v[k] : v[k] + 100
            end
        end
        return s
    end
    sci, _ = code_structured(gated_loop_acc, Tuple{Bool, Vector{Int}, Int}) |> only
    @test count_stmts(sci.entry, s -> iscall_to(s, :memoryrefget)) >= 1  # body present, not dropped
    for (c, v, n) in ((false, [1,2,3], 3), (true, [1,2,3], 3),
                      (false, [5,6,7,8], 4), (true, [1], 0))
        @test execute(sci, c, v, n) == gated_loop_acc(c, v, n)
    end

    # A `||`-guarded body that itself early-returns (body has an internal
    # region-exit reaching past the guard's continuation).
    f_ret = (a::Bool, b::Bool, x::Int) -> (if opaque(a) || opaque(b); x > 0 && return x; end; -1)
    sci_r, _ = code_structured(f_ret, Tuple{Bool, Bool, Int}) |> only
    for (a, b, x) in ((true, false, 5), (true, false, -5), (false, false, 5))
        @test execute(sci_r, a, b, x) == f_ret(a, b, x)
    end

    # Two sequential ||-guards threading a value through the shared merge.
    function f_seq(a::Bool, b::Bool, n::Int)
        if opaque(a) || opaque(b); t = n + 1; else; t = n - 1; end
        if opaque(a) || opaque(b); return t * 2; end
        return t
    end
    sci_s, _ = code_structured(f_seq, Tuple{Bool, Bool, Int}) |> only
    for a in (false, true), b in (false, true)
        @test execute(sci_s, a, b, 3) == f_seq(a, b, 3)
    end
end

@testset "sequential ifs sharing a condition in a loop" begin
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    @noinline sink(x) = (Base.donotdelete(x); nothing)
    function seq_ifs_loop(n::Int, c::Bool)
        cond = opaque(c); acc = 0
        for kt in 1:n
            if cond; sink(kt); end
            if cond; acc += kt; end
        end
        return acc
    end
    @test @roundtrip seq_ifs_loop(5, true)
    @test @roundtrip seq_ifs_loop(5, false)
    @test @roundtrip seq_ifs_loop(0, true)
end

@testset "early return inside a branch (virtual exit)" begin
    f_early = (x::Int, y::Int) -> (x > y ? (return y * x) : nothing; y - x)
    @test @roundtrip f_early(5, 3)
    @test @roundtrip f_early(3, 5)
end

@testset "throw inside a loop and inside a branch" begin
    function loop_throw(a::Vector{Float32}, n::Int)
        acc = 0.0f0
        for k in 1:n
            x = @inbounds a[k]
            x < 0.0f0 && throw(DomainError(x))
            acc += x
        end
        return acc
    end
    sci, _ = code_structured(loop_throw, Tuple{Vector{Float32}, Int}) |> only
    @test execute(sci, Float32[1, 2, 3], 3) == 6.0f0
    @test_throws DomainError execute(sci, Float32[1, -2, 3], 3)

    branch_throw = (x::Int) -> (x < 0 ? throw(DomainError(x)) : x + 1)
    sci2, _ = code_structured(branch_throw, Tuple{Int}) |> only
    @test execute(sci2, 4) == 5
    @test_throws DomainError execute(sci2, -1)
end

@testset "early return inside a loop" begin
    # A `return` block inside a loop is a region-exit (no successors), like a
    # throw. The single-exiting latch routes it through the post-loop dispatch (a
    # multi-exit loop), where it is re-emitted after the loop — never collapsed to
    # a bare break (which would drop the returned value).
    function ret_in_loop(v::Vector{Int}, n::Int)
        acc = 0
        for i in 1:n
            v[i] < 0 && return -i
            acc += v[i]
        end
        return acc
    end
    sci, _ = code_structured(ret_in_loop, Tuple{Vector{Int}, Int}) |> only
    for (v, n) in ((Int[1,2,3], 3), (Int[1,-2,3], 3), (Int[-1,2], 2), (Int[1,2], 0))
        @test execute(sci, v, n) == ret_in_loop(v, n)
    end

    function ret_while(n::Int)
        i = 0
        while i < n
            i += 1
            i == 3 && return 100
        end
        return i
    end
    sci2, _ = code_structured(ret_while, Tuple{Int}) |> only
    for n in (1, 5, 2, 0)
        @test execute(sci2, n) == ret_while(n)
    end

    # return AND throw both inside the same loop — two distinct secondary exits.
    function ret_and_throw(v::Vector{Int}, n::Int)
        s = 0
        for i in 1:n
            v[i] == 0 && throw(DomainError(i))
            v[i] < 0 && return -i
            s += v[i]
        end
        return s
    end
    sci3, _ = code_structured(ret_and_throw, Tuple{Vector{Int}, Int}) |> only
    @test execute(sci3, Int[1, 2, 3], 3) == 6
    @test execute(sci3, Int[1, -2, 3], 3) == -2
    @test_throws DomainError execute(sci3, Int[1, 0, 3], 3)
end

@testset "promotion: counted for, step range, while" begin
    @test @roundtrip ((n::Int) -> (acc = 0; for i in 1:n; acc += i; end; acc))(5)
    @test @roundtrip ((n::Int) -> (i = 0; while i < n; i += 1; end; i))(5)
    @test @roundtrip ((n::Int) -> (acc = 0; for i in 1:2:n; acc += i; end; acc))(7)
    @test @roundtrip ((n::Int) -> (i = 0; while i <= n; i += 1; end; i))(4)
end

@testset "promotion recognizes intrinsics by identity, not name" begin
    @test @roundtrip AliasedIntrinsics.misnamed(4)
    sci, _ = code_structured(AliasedIntrinsics.renamed, Tuple{Int}) |> only
    @test count_stmts(sci.entry, s -> s isa ForOp) == 1
    for n in (0, 1, 5)
        @test execute(sci, n) == AliasedIntrinsics.renamed(n)
    end
end

@static if VERSION >= v"1.12-"
@testset "promotion reads constants in the IR's world" begin
    ir, _ = only(code_ircode(ReboundIntrinsic.counted, Tuple{Int}))
    Core.eval(ReboundIntrinsic, :(const cmp = Core.Intrinsics.sle_int))
    @test execute(StructuredIRCode(ir), 4) == 4
end
end

@testset "while loop carrying a counter + accumulator promotes to a ForOp" begin
    # Regression: `while k<n; k+=1; s+=k; end` carries two values. WhileOp→ForOp
    # promotion folds the induction increment into `0:1:n`, but `s += k` reads the
    # post-increment value `k`; dropping that increment statement left the read
    # dangling ("SSA used but not defined"). The increment now survives — remapped
    # to the induction variable — whenever something other than the IV carry reads
    # it. (Found by `res/fuzz.jl`'s `while`-outer-loop coverage.)
    wacc(n::Int) = (s = 0; k = 0; while k < n; k += 1; s += k; end; s)
    sci, _ = code_structured(wacc, Tuple{Int}) |> only
    @test count_stmts(sci.entry, s -> s isa ForOp) == 1     # promotes (the bug threw before this)
    for n in (0, 1, 2, 3, 5, 10)
        @test execute(sci, n) == wacc(n)
    end
    # Accumulating the *pre*-increment counter (the IV is read directly, not via
    # the increment) — the sibling shape, must also stay correct.
    wacc2(n::Int) = (s = 0; k = 0; while k < n; s += k; k += 1; end; s)
    sci2, _ = code_structured(wacc2, Tuple{Int}) |> only
    for n in (0, 1, 3, 6, 10)
        @test execute(sci2, n) == wacc2(n)
    end
end

@testset "a loop variable undefined on entry" begin
    # Lowered loop-header phis leave an undefined init unassigned.
    phis_ok(sci) = let phis = filter(s -> s isa PhiNode, Core.Compiler.IRCode(sci).stmts.stmt)
        any(p -> !all(k -> isassigned(p.values, k), eachindex(p.values)), phis) &&
            !any(p -> any(k -> isassigned(p.values, k) && p.values[k] isa Undef,
                          eachindex(p.values)), phis)
    end

    # A variable first assigned inside the loop enters it as `Undef`, whichever loop
    # op the loop becomes.
    function undef_entry_loop(n)
        local z
        i = 0
        while true
            i += 1
            i > n && return z
            z = i * 2
        end
    end
    function undef_entry_for(n)
        local z
        i = 0
        while i < n
            i += 1
            z = i * 2
        end
        z
    end
    function undef_entry_while(n)
        local z
        i = 1
        while i * i < n
            z = i
            i += 2
        end
        z
    end
    for (f, Op) in ((undef_entry_loop, LoopOp), (undef_entry_for, ForOp),
                    (undef_entry_while, WhileOp))
        sci, _ = code_structured(f, Tuple{Int}) |> only
        @test count_stmts(sci.entry, s -> s isa Op) == 1
        for n in (3, 20)
            @test execute(sci, n) == f(n)
        end
        @test_throws UndefVarError execute(sci, 0)
        @test phis_ok(sci)
    end

    # An induction variable undefined on entry has no lower bound, so the loop is
    # not promoted to a ForOp.
    add(a, b) = Expr(:call, GlobalRef(Core.Intrinsics, :add_int), a, b)
    sci = StructuredIRCode(build_ir([
        (stmts=[(GotoNode(2), Any)], succs=[2]),
        (stmts=[(PhiNode(Int32[3], Any[SSAValue(6)]), Int),                  # %2 i
                (PhiNode(Int32[1, 3], Any[0, SSAValue(7)]), Int),            # %3
                (Expr(:call, GlobalRef(Core.Intrinsics, :slt_int), SSAValue(2), Argument(2)), Bool),
                (GotoIfNot(SSAValue(4), 4), Any)], succs=[4, 3]),
        (stmts=[(add(SSAValue(2), 1), Int),
                (add(SSAValue(3), 1), Int),
                (GotoNode(2), Any)], succs=[2]),
        (stmts=[(ReturnNode(SSAValue(3)), Any)], succs=Int[]),
    ], Any[Any, Int]))
    @test count_stmts(sci.entry, s -> s isa ForOp) == 0
    @test phis_ok(sci)
end

@testset "empty counted while-loop returns its init, not its bound" begin
    # A `while x < n` whose induction value starts at or above the bound runs zero
    # times, so the loop result must be the init (the unchanged IV), not the bound.
    # A ForOp does not carry its IV as a result, so promotion keeps the escaping IV
    # as an ordinary carried value rather than dropping it and aliasing the post-loop
    # read to `upper`. That alias would equal the IV only when the body ran; for the
    # empty case (init >= bound) the final IV is the init. The carried value reads
    # back normally and is correct for both the empty (= init) and non-empty
    # (= last continue = upper) cases. The standing loop fuzzers all start the IV
    # below the bound (`for k in 1:n`), so they miss this; the exec-over-empty checks
    # below are what guard it, so never remove them.
    fixed(n::Int) = (x = 100; while x < n; x += 1; end; x)
    ir, _ = only(code_ircode(fixed, Tuple{Int}))
    # init=100 spans empty (n ≤ 100) and non-empty (n > 100); both promote modes.
    for promote in (false, true)
        sci = StructuredIRCode(ir; promote)
        for n in (0, 5, 50, 100, 150, 200)
            @test execute(sci, n) == fixed(n)
        end
    end
    # The IV escapes (`return x`) and is kept as a carry, so this is a correct ForOp
    # (lower = init 100, step 1).
    sci_p = StructuredIRCode(ir; promote=true)
    @test count_stmts(sci_p.entry, s -> s isa WhileOp) == 0
    @test count_stmts(sci_p.entry, s -> s isa ForOp) == 1
    for_op = only(filter(x -> x isa ForOp, collect(statements(sci_p.entry.body))))
    @test for_op.lower == 100
    @test for_op.step == 1

    # Inclusive bound (`while x <= n`): empty when init > n (so n < 100 is empty).
    fixed_le(n::Int) = (x = 100; while x <= n; x += 1; end; x)
    for n in (0, 50, 99, 100, 101, 200)
        @test @roundtrip fixed_le(n)
    end

    # Step > 1 with a separate accumulator carried alongside the escaping IV. Both
    # the kept IV carry and the accumulator ride the ForOp correctly.
    fixed_step(n::Int) = (x = 100; s = 0; while x < n; s += x; x += 2; end; x + s)
    for n in (0, 50, 100, 150, 200)
        @test @roundtrip fixed_step(n)
    end

    # A genuine counted `for i in 1:n` does not read `i` after the loop (Julia
    # scopes it out), so the IV is dropped and it still promotes to a ForOp. The
    # empty range (n < 1) confirms the well-behaved counted case is untouched.
    forsum(n::Int) = (acc = 0; for i in 1:n; acc += i; end; acc)
    ir_for, _ = only(code_ircode(forsum, Tuple{Int}))
    sci_for = StructuredIRCode(ir_for; promote=true)
    @test count_stmts(sci_for.entry, s -> s isa ForOp) == 1   # still promotes
    for n in (-1, 0, 1, 5)
        @test execute(sci_for, n) == forsum(n)
    end
end

@testset "escaping IV ForOp: step>1 and inclusive <= bound" begin
    # The kept-IV ForOp must be correct for a non-unit step and for an inclusive
    # `<=` bound (which adjusts the range control by +1 but not the carried value).

    # step 2: counted2(5) iterates i=0,2,4 then continues to 6 (the first value
    # failing i<5), so the escaping IV result is 6; empty (n≤0) returns init 0.
    counted2(n::Int) = (i = 0; while i < n; i += 2; end; i)
    ir2, _ = only(code_ircode(counted2, Tuple{Int}))
    sci2 = StructuredIRCode(ir2; promote=true)
    @test count_stmts(sci2.entry, s -> s isa ForOp) == 1
    let for_op = only(filter(x -> x isa ForOp, collect(statements(sci2.entry.body))))
        @test for_op.lower == 0
        @test for_op.step == 2
    end
    for n in (-3, 0, 1, 2, 5, 6, 50, 200)
        @test execute(sci2, n) == counted2(n)
    end
    @test counted2(5) == 6 && execute(sci2, 5) == 6   # the step-2 exit value

    # inclusive `<=` whose IV escapes: `while i<=n; i+=1; return i`. The exclusive
    # range upper is n+1, but the carried IV value is unaffected by that adjustment.
    counted_le(n::Int) = (i = 0; while i <= n; i += 1; end; i)
    irle, _ = only(code_ircode(counted_le, Tuple{Int}))
    scile = StructuredIRCode(irle; promote=true)
    @test count_stmts(scile.entry, s -> s isa ForOp) == 1
    for n in (-3, -1, 0, 1, 2, 5, 50, 200)
        @test execute(scile, n) == counted_le(n)
    end
end

@testset "the core walk emits only LoopOp (promotion is a post-pass)" begin
    # With `promote=false`, every loop must be a generic LoopOp — no ForOp/WhileOp
    # leaks from the core walk. (With promotion they become For/While; that path is
    # exercised above.) Counted, step-range, and condition loops all qualify.
    function no_forwhile(blk::Block)
        for (_, e) in blk.body
            (e.stmt isa ForOp || e.stmt isa WhileOp) && return false
            if e.stmt isa ControlFlowOp
                for b in IRStructurizer.blocks(e.stmt)
                    no_forwhile(b) || return false
                end
            end
        end
        return true
    end
    for f in (n -> (acc = 0; for i in 1:n; acc += i; end; acc),
              n -> (i = 0; while i < n; i += 1; end; i),
              n -> (acc = 0; for i in 1:2:n; acc += i; end; acc))
        ir, _ = only(code_ircode(f, Tuple{Int}))
        sci_raw = StructuredIRCode(ir; promote=false)
        @test no_forwhile(sci_raw.entry)
        # ...and with promotion the same IR yields a counted ForOp somewhere.
        sci_pro = StructuredIRCode(ir; promote=true)
        @test !no_forwhile(sci_pro.entry)
    end
end

@testset "escaping IV read through a PiNode" begin
    # while i < upper; i += 1; end; return PiNode(i, Int)
    # Keep the PiNode explicit: inference may remove a redundant type assertion.
    ir = build_ir([
        (stmts=[(GotoNode(2), Any)], succs=[2]),
        (stmts=[(PhiNode(Int32[1, 3], Any[Argument(2), SSAValue(5)]), Int),
                (Expr(:call, GlobalRef(Base, :slt_int), SSAValue(2), Argument(3)), Bool),
                (GotoIfNot(SSAValue(3), 4), Any)], succs=[4, 3]),
        (stmts=[(Expr(:call, GlobalRef(Base, :add_int), SSAValue(2), 1), Int),
                (GotoNode(2), Any)], succs=[2]),
        (stmts=[(PiNode(SSAValue(2), Int), Int),
                (ReturnNode(SSAValue(7)), Any)], succs=Int[]),
    ], Any[Any, Int, Int])
    CC.verify_ir(ir)
    sci = StructuredIRCode(ir)
    for (lower, upper) in ((5, 2), (2, 2), (2, 5))
        @test execute(sci, lower, upper) == max(lower, upper)
    end
end

@testset "single-predecessor argument escaping a loop" begin
    # A one-input phi copies the header IV into the body. Its last value escapes
    # the loop, so binding the phi must define the id reserved by emit_loop!.
    ir = build_ir([
        (stmts=[(GotoNode(2), Any)], succs=[2]),
        (stmts=[(PhiNode(Int32[1, 4], Any[0, SSAValue(5)]), Int),
                (GotoNode(3), Any)], succs=[3]),
        (stmts=[(PhiNode(Int32[2], Any[SSAValue(2)]), Int),
                (Expr(:call, GlobalRef(Base, :add_int), SSAValue(4), 1), Int),
                (Expr(:call, GlobalRef(Base, :slt_int), SSAValue(5), Argument(2)), Bool),
                (GotoIfNot(SSAValue(6), 5), Any)], succs=[5, 4]),
        (stmts=[(GotoNode(2), Any)], succs=[2]),
        (stmts=[(ReturnNode(SSAValue(4)), Any)], succs=Int[]),
    ], Any[Any, Int])
    CC.verify_ir(ir)
    for promote in (false, true), mux in (false, true)
        m = IRStructurizer.ingest(CC.copy(ir))
        if mux
            # The continuation mux also leaves a single-predecessor argument.
            IRStructurizer.single_entry_mux!(m, [IRStructurizer.EdgeRef(2, :goto)])
        end
        sci = IRStructurizer.lift_mcfg(m; promote)
        for n in (0, 1, 3)
            @test execute(sci, n) == max(0, n - 1)
        end
    end
end

@testset "single-predecessor argument of a constant" begin
    # Block 2's phi has one predecessor and a constant operand: the walk copies the
    # constant to the phi's id. Anchoring that copy's line to itself made
    # `resolve_line` loop forever (on 1.12+, every statement has a line entry).
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 3), Any)],                     succs=[2, 3]),
        (stmts=[(PhiNode(Int32[1], Any[7]), Int),
                (GotoNode(4), Any)],                                   succs=[4]),
        (stmts=[(GotoNode(4), Any)],                                   succs=[4]),
        (stmts=[(PhiNode(Int32[2, 3], Any[SSAValue(2), 0]), Int),
                (ReturnNode(SSAValue(5)), Any)],                       succs=Int[]),
    ], Any[Any, Bool])
    sci = StructuredIRCode(ir)
    selfanchored = any(((k, v),) -> v == k, sci.line_map)
    @test !selfanchored
    if !selfanchored            # lowering would never return
        @test execute(sci, true) === 7
        @test execute(sci, false) === 0
    end
end

@testset "PiNode carry and :invoke closure" begin
    # A value used through a PiNode after the loop must be threaded out.
    function pi_carry(v::Vector{Any}, n::Int)
        x = 0
        for i in 1:n
            x = v[i]::Int
        end
        return x + 1
    end
    @test @roundtrip pi_carry(Any[1, 2, 3], 3)

    # A closure applied via :invoke counts its callee operand as a use.
    function invoke_closure(n::Int)
        acc = 0
        f = y -> y + 1
        for i in 1:n
            acc += f(i)
        end
        return acc
    end
    @test @roundtrip invoke_closure(4)
end

@testset "irreducible CFGs (entry multiplexer)" begin
    # `@goto` produces multi-entry SCCs that no block dominates — irreducible.
    # normalize_cf inserts one entry multiplexer (the disc-as-carried-value form):
    # the SCC's entry blocks collapse to a single loop header that dispatches on a
    # discriminator carry, and the latch unifies the back edges. The result is a
    # plain reducible LoopOp the existing lift handles (previously rejected as
    # unstructurable).

    # Canonical 2-entry SCC {BB3,BB5,BB6,BB8}, entries BB3 (from BB1) and BB6
    # (from BB2). Only terminating inputs (x<=0 with small y oscillates forever,
    # in the source too).
    function irreducible(x::Int, y::Int)
        if x > 0; @goto L2; end
        @label L1; y += x; if y > 100; return y; end; @goto L2_body
        @label L2; @label L2_body; y += 1; if y > 100; return y; end; @goto L1
    end
    for (x, y) in ((1, 50), (5, 200), (3, 98), (2, -10), (0, 0), (-1, 200), (100, 1))
        @test @roundtrip irreducible(x, y)
    end

    # 3-entry SCC → an N=3 discriminator compare-chain in the mux dispatch.
    function irr3(s::Int, n::Int)
        acc = 0
        s == 0 && @goto A
        s == 1 && @goto B
        @goto C
        @label A; acc += 1; acc > n && return acc; @goto B
        @label B; acc += 2; acc > n && return acc; @goto C
        @label C; acc += 3; acc > n && return acc; @goto A
    end
    for (s, n) in ((0, 10), (1, 10), (2, 10), (0, 0), (1, 5), (2, 100))
        @test @roundtrip irr3(s, n)
    end

    # Structural: the SCC collapses to exactly one LoopOp (irreducible loops stay
    # LoopOp — no While/For promotion, there is no single counting condition), and
    # structurization succeeds + validates (no UnstructuredControlFlowError).
    sci, _ = code_structured(irreducible, Tuple{Int, Int}) |> only
    @test count_stmts(sci.entry, s -> s isa LoopOp) == 1
    sci3, _ = code_structured(irr3, Tuple{Int, Int}) |> only
    @test count_stmts(sci3.entry, s -> s isa LoopOp) == 1

    # Determinism: structurizing the same IR twice yields the same shape — the mux
    # sorts its entries, so no iteration-order nondeterminism leaks in.
    ir, _ = only(code_ircode(irr3, Tuple{Int, Int}))
    s1 = sprint(show, MIME"text/plain"(), StructuredIRCode(ir))
    s2 = sprint(show, MIME"text/plain"(), StructuredIRCode(ir))
    @test s1 == s2
end

@testset "nested gated bodies (continuation multiplexer)" begin
    # The canonical case the continuation multiplexer fixes. A `||`-guarded body
    # whose body is ITSELF a `||`-guarded body, inside a loop carrying an
    # accumulator — historically a silent miscompile. Every multi-pred continuation
    # is collapsed to single-entry upstream, so the ordinary IfOp lift handles
    # arbitrary nesting with no shape-matching.
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    function nested_gated(a::Bool, b::Bool, n::Int)
        s = 0
        for k in 1:n
            if opaque(a) || k > 1
                if opaque(b) || k > 2
                    s += k
                end
            end
        end
        return s
    end
    sci, _ = code_structured(nested_gated, Tuple{Bool, Bool, Int}) |> only  # must not throw
    # The innermost guarded write `s += k` (a memoryref-free add into the carry)
    # is emitted once, not duplicated per guard arm.
    @test count_stmts(sci.entry, s -> iscall_to(s, :add_int)) == 2   # `s += k` and the IV `k += 1`
    for a in (false, true), b in (false, true), n in (0, 1, 3, 5)
        @test execute(sci, a, b, n) == nested_gated(a, b, n)
    end

    # Three-deep nesting, value-producing (each level contributes to the result).
    function nest3(a::Bool, b::Bool, c::Bool, x::Int)
        r = 0
        if opaque(a) || x > 0
            if opaque(b) || x > 1
                if opaque(c) || x > 2
                    r = x * 10
                end
            end
        end
        return r
    end
    sci3, _ = code_structured(nest3, Tuple{Bool, Bool, Bool, Int}) |> only
    for a in (false, true), b in (false, true), c in (false, true), x in (-1, 0, 1, 2, 3)
        @test execute(sci3, a, b, c, x) == nest3(a, b, c, x)
    end
end

@testset "a branch whose two edges reach the same continuation entry" begin
    # SparseColumnPivotedQR's `_usolve!`: continues out of nested branches. Muxing an
    # inner continuation redirects both edges of one branch into the mux, which is
    # then an entry of an outer continuation; each edge must be routed through the
    # outer mux once.
    function usolve!(z::Vector{Float64}, Rp::Vector{Int}, Ri::Vector{Int}, Rx::Vector{Float64},
                     n::Int, tol::Float64)
        for k in n:-1:1
            rc1 = Rp[k]; rc2 = Rp[k + 1] - 1
            if rc2 >= rc1 && Ri[rc2] == k
                d = Rx[rc2]
                if abs(d) <= tol || d == 0
                    z[k] = 0.0
                    continue
                end
                z[k] /= d
            else
                diag_p = 0
                for p in rc1:rc2
                    if Ri[p] == k
                        diag_p = p
                        break
                    end
                end
                if diag_p == 0
                    z[k] = 0.0
                    continue
                end
                d = Rx[diag_p]
                if abs(d) <= tol || d == 0
                    z[k] = 0.0
                    continue
                end
                z[k] /= d
                zk = z[k]
                for p in rc1:rc2
                    p == diag_p && continue
                    z[Ri[p]] -= Rx[p] * zk
                end
            end
        end
        return z
    end
    sci, _ = code_structured(usolve!, Tuple{Vector{Float64}, Vector{Int}, Vector{Int},
                                            Vector{Float64}, Int, Float64}) |> only
    # columns: the diagonal last, first, absent, or zero
    Rp = [1, 2, 4, 6, 7, 9]
    Ri = [1, 1, 2, 3, 1, 3, 4, 2]
    for Rx in ([2.0, 0.5, 3.0, 4.0, 1.0, 0.0, 5.0, 1.5], [1.0, 2.0, 0.0, 1.0, 1.0, 2.0, 0.0, 3.0]),
        tol in (0.0, 1.5)
        @test execute(sci, ones(5), Rp, Ri, Rx, 5, tol) == usolve!(ones(5), Rp, Ri, Rx, 5, tol)
    end
end

@testset "a branch whose two edges enter a loop header" begin
    # Block 1 branches to the loop header on both edges; the pre-header must take
    # each edge once.
    ir = build_ir([
        (stmts=[(GotoIfNot(Argument(2), 2), Any)],                            succs=[2]),
        (stmts=[(PhiNode(Int32[1, 3], Any[0, SSAValue(5)]), Int),
                (Expr(:call, GlobalRef(Base, :slt_int), SSAValue(2), Argument(3)), Bool),
                (GotoIfNot(SSAValue(3), 4), Any)],                            succs=[3, 4]),
        (stmts=[(Expr(:call, GlobalRef(Base, :add_int), SSAValue(2), 1), Int),
                (GotoNode(2), Any)],                                          succs=[2]),
        (stmts=[(ReturnNode(SSAValue(2)), Any)],                              succs=Int[]),
    ], Any[Any, Bool, Int])
    sci = StructuredIRCode(ir)
    @test execute(sci, true, 5) === 5
    @test execute(sci, false, 3) === 3
end

@testset "a counted loop with a break stays a LoopOp" begin
    # A `break` inside a `for`/`while` is a dynamic exit a counted ForOp / a
    # condition WhileOp can't represent: promoting it left a stray BreakOp in the
    # promoted body whose exit placeholder leaked at unstructurize (a crash).
    # promote_loops! now keeps such a loop a LoopOp (count_breaks > 1).
    @noinline opaque(b::Bool) = Base.compilerbarrier(:type, b)::Bool
    function for_break(p::Bool, n::Int)
        s = 0
        for k in 1:n
            s += k
            if opaque(p) && k > 3; break; end
        end
        return s
    end
    sci, _ = code_structured(for_break, Tuple{Bool, Int}) |> only
    @test count_stmts(sci.entry, s -> s isa ForOp) == 0   # not promoted
    @test count_stmts(sci.entry, s -> s isa LoopOp) == 1
    for p in (false, true), n in (0, 2, 4, 6)
        @test execute(sci, p, n) == for_break(p, n)
    end

    function while_break(n::Int)
        i = 0; acc = 0
        while i < n
            i += 1
            i == 4 && break
            acc += i
        end
        return acc
    end
    sci2, _ = code_structured(while_break, Tuple{Int}) |> only
    for n in (0, 2, 4, 6, 10)
        @test execute(sci2, n) == while_break(n)
    end
end

@testset "secondary loop exits through a pass-through block" begin
    # A loop whose escape is an early `return`/`throw` reached via the `||`
    # short-circuit — the exit edge lands on a `goto #ret` pass-through, not the
    # return block itself. Collapsing that edge to a bare break (which skips the
    # return) silently miscompiled; the single-exiting latch now routes every exit
    # through the post-loop dispatch, where the return is re-emitted after the
    # loop. Found by fuzzing (exec vs direct).
    @noinline opaque(b::Bool) = Base.compilerbarrier(:type, b)::Bool
    function early_ret_in_loop(p::Bool, n::Int)
        s = 0
        for k in 1:n
            if k > 2 || opaque(p)
                return s + 2
            end
            s += k
        end
        return s
    end
    sci, _ = code_structured(early_ret_in_loop, Tuple{Bool, Int}) |> only
    for p in (false, true), n in (0, 1, 2, 3, 5)
        @test execute(sci, p, n) == early_ret_in_loop(p, n)
    end

    # A shared return reached from BOTH `||` arms, with a non-trivial returned
    # value — its operand is threaded out as a latch arg and the return is
    # re-emitted once in the post-loop dispatch.
    function shared_ret(a::Bool, b::Bool, n::Int)
        acc = 0
        for k in 1:n
            if opaque(a) || opaque(b)
                return acc * 10 + k
            end
            acc += k
        end
        return acc
    end
    sci2, _ = code_structured(shared_ret, Tuple{Bool, Bool, Int}) |> only
    for a in (false, true), b in (false, true), n in (0, 1, 3)
        @test execute(sci2, a, b, n) == shared_ret(a, b, n)
    end

    # A shared exit path that itself contains a branch (the returned value is a
    # ternary), reached from both `||` arms — the computed value is threaded out
    # as a latch arg and the return is re-emitted once after the loop.
    function shared_branch_exit(a::Bool, b::Bool, c::Bool, n::Int)
        acc = 0
        for k in 1:n
            if opaque(a) || opaque(b)
                r = opaque(c) ? acc + 100 : acc + 200
                return r + k
            end
            acc += k
        end
        return acc
    end
    sci4, _ = code_structured(shared_branch_exit, Tuple{Bool, Bool, Bool, Int}) |> only
    for a in (false, true), b in (false, true), c in (false, true), n in (0, 1, 3)
        @test execute(sci4, a, b, c, n) == shared_branch_exit(a, b, c, n)
    end
end

@testset "multi-entry shapes (exec vs direct)" begin
    # A curated, deterministic set of short-circuit / nested-guard / guard-in-loop
    # / guard-with-early-exit shapes — two latent silent miscompiles once lived in
    # these families. A fixed function list over enumerated inputs, asserting
    # structurize→unstructurize→execute == direct (the generative fuzzer that
    # first surfaced these lives in the dev scripts, not the suite).
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool

    fns = Any[
        # mixed &&/|| chains
        (x::Int, y::Int, z::Int) -> ((opaque(x > 0) || y > 0) && z > 0) ? 1 : 2,
        (x::Int, y::Int, z::Int) -> (opaque(x > 0) && (y > 0 || z > 0)) ? 1 : 2,
        (x::Int, y::Int, z::Int) -> (x > 0 || y > 0 || z > 0) ? 1 : 2,
        (x::Int, y::Int, z::Int) -> (x > 0 && y > 0 && z > 0) ? 1 : 2,
        # guard in a loop feeding a carried accumulator
        (a::Bool, n::Int) -> (s = 0; for k in 1:n; if opaque(a) || k > 2; s += k; end; end; s),
        # nested guards in a loop
        (a::Bool, b::Bool, n::Int) -> (s = 0; for k in 1:n
            if opaque(a) || k > 1; if opaque(b) || k > 2; s += k * k; end; end; end; s),
        # guard whose body early-returns
        (a::Bool, b::Bool, x::Int) -> (if opaque(a) || opaque(b); x > 0 && return x; end; -1),
        # value defined in one guard, used in a later guard (undef phi slot)
        (c1::Bool, c2::Bool, n::Int) -> (local t; if c1 || c2; t = n + 1; end;
                                         s = 0; if c1 || c2; s = t; end; s),
        # sequential guards threading a value through the shared merge
        (a::Bool, b::Bool, n::Int) -> (if opaque(a) || opaque(b); t = n + 1; else; t = n - 1; end;
                                       if opaque(a) || opaque(b); return t * 2; end; t),
    ]
    for f in fns
        m = only(methods(f))
        nparams = m.nargs - 1
        sci = (code_structured(f) |> only).first
        # Enumerate booleans for Bool params, small ints otherwise.
        ptypes = [fieldtype(Base.tuple_type_tail(m.sig), i) for i in 1:nparams]
        choices = [pt === Bool ? (false, true) : (-1, 0, 1, 2, 5) for pt in ptypes]
        for combo in Iterators.product(choices...)
            @test execute(sci, combo...) == f(combo...)
        end
    end
end

@testset "multi-exit loops via the single-exiting latch (lf5 / sentinel / inner-break)" begin
    # The single-exiting latch (normalize_cf) unifies a loop's ≥2 exit edges into
    # one back + one exit edge in reduce form, so a multi-exit loop lifts as a
    # plain LoopOp with the escapees carried as BreakOp results. These shapes
    # silently miscompiled before the latch (the loop fuzzer measured 55 silent);
    # the curated set below is the standing guard (the generative loop fuzzer that
    # measured those miscompiles lives in the dev scripts, not the suite).

    # lf5: two breaks, the second carrying a fresh value, read after the loop.
    function lf5(p::Bool, n::Int)
        s = 0
        for k in 1:n
            if k > 4; break; end
            if k > 2; s = 0; break; end
            s += k
        end
        return s
    end
    sci, _ = code_structured(lf5, Tuple{Bool, Int}) |> only
    for p in (false, true), n in (0, 1, 3, 5, 8)
        @test execute(sci, p, n) == lf5(p, n)
    end

    # sentinel-break: break carrying the sentinel out, used post-loop.
    function sentinel_break(v::Vector{Int}, n::Int)
        found = -1
        for i in 1:n
            if v[i] == 0; found = i; break; end
            if v[i] < 0; break; end
        end
        return found
    end
    sci2, _ = code_structured(sentinel_break, Tuple{Vector{Int}, Int}) |> only
    for (v, n) in ((Int[1, 0, 2], 3), (Int[1, 2, 3], 3), (Int[-1, 0], 2), (Int[1], 0))
        @test execute(sci2, v, n) == sentinel_break(v, n)
    end

    # inner-loop-break: a guarded outer break + an inner loop with a break-with-
    # value (the nested-latch interaction; the _lf45 / "case B" regressor).
    function inner_break(p::Bool, n::Int)
        s = 0
        for k in 1:n
            if p; if k > 4; break; end; s += 3; end
            for j in 1:k
                if k > 4; s = 3; break; end
                s += k
            end
        end
        return s
    end
    sci3, _ = code_structured(inner_break, Tuple{Bool, Int}) |> only
    for p in (false, true), n in (0, 1, 3, 5)
        @test execute(sci3, p, n) == inner_break(p, n)
    end
end

@testset "branch-selected init read after the loop (pre-header)" begin
    # An if/else (not a ternary) writes a variable whose SSA phi sits at the loop
    # header — the branch's merge block *is* the loop header — and the variable is
    # read after the loop. Without the pre-header (normalize_one_preheader!) the
    # read saw the *entry* value (the branch selection), not the loop result: the
    # IfOp parked the entry value at the header phi id and the loop result at a
    # fresh id, but post-loop uses still referenced the header phi id. The
    # pre-header routes the entry edges through a separate block so the IfOp yields
    # into the pre-header args (the loop init) while the loop result stays on the
    # header arg — the value `return`ed. Silent miscompile before the fix
    # (ISSUES.md #2, "meh1"); the standing fuzzers use ternary inits and missed it.
    function meh1(c::Bool, n::Int)
        if c; x = 10; else; x = 100; end   # if-merge coincides with the while header
        while x < n; x += 1; end
        return x
    end
    # The pre-header fix lives in the core lift, so assert it across every n,
    # including the empty-loop cases (init already >= bound) where the result is the
    # branch selection (10/100) itself. Both promote modes are checked: the empty
    # case once exposed a separate promotion bug where an empty counted while-loop
    # returned its bound instead of its init, now closed by keeping the escaping IV
    # as a carry, so promote=true must agree across the full range too.
    ir_np, _ = only(code_ircode(meh1, Tuple{Bool, Int}))
    for promote in (false, true)
        sci_m = StructuredIRCode(ir_np; promote)
        for c in (false, true), n in (0, 5, 50, 200)
            @test execute(sci_m, c, n) == meh1(c, n)
        end
    end
    # The literal ISSUES.md #2 repro through the full pipeline: at n=200 the loop
    # runs for both arms, so the result is the loop output (200), not the entry
    # value (10/100) — the miscompile the pre-header closed.
    sci, _ = code_structured(meh1, Tuple{Bool, Int}) |> only
    @test execute(sci, true, 200) == 200
    @test execute(sci, false, 200) == 200

    # Counted-for outer loop carrying a branch-selected accumulator (the loop runs
    # `1:n` independent of the init, so promotion is well-behaved here).
    function meh_for(c::Bool, n::Int)
        if c; s = 10; else; s = 100; end
        for _ in 1:n; s += 1; end
        return s
    end
    sci2, _ = code_structured(meh_for, Tuple{Bool, Int}) |> only
    for c in (false, true), n in (0, 1, 5)
        @test execute(sci2, c, n) == meh_for(c, n)
    end
end

@testset "loop escape arguments are fed only where they can be read" begin
    # `reduce_loop!` adds a latch argument for every loop-internal value used
    # after the loop. Lists, per single-exiting latch of the normalized MCFG, every
    # edge into it as its source block, the `shouldRepeat` operand and the
    # operands for those escape arguments (the latch args after `shouldRepeat`).
    function latch_edges(m)
        res = []
        for (L, b) in enumerate(m.blocks)
            t = b.term
            t isa IRStructurizer.MCondBr && t.cond isa SSAValue || continue
            i = findfirst(s -> s.id == t.cond.id, b.body)
            i === nothing && continue
            st = b.body[i].stmt
            (Meta.isexpr(st, :call) && st.args[1] === Core.:(===) && st.args[3] === 1 &&
             st.args[2] isa SSAValue && st.args[2].id in b.args) || continue
            srpos = findfirst(==(st.args[2].id), b.args)
            edges = []
            for src in 1:length(m.blocks), r in IRStructurizer.edge_refs(m, src, L)
                e = IRStructurizer.edge_of(m, r)
                push!(edges, (; src, sr=e.args[srpos], escapes=e.args[srpos+1:end]))
            end
            push!(res, (; header=t.t.target, edges))
        end
        return res
    end
    isundef(x) = x isa IRStructurizer.Undef
    latch_of(ir) = only(latch_edges(IRStructurizer.normalize_cf(ir)))

    # Early returns read the iteration-start `z`/`out` (header phis), the normal
    # exit reads the updated ones. No escape argument is read after a back edge.
    function newton(x, z)
        out = x*z - 1.0
        isfinite(out) || return z, out, false
        for _ in 1:100
            abs(out) < 1e6 || return z, out, false
            dz = out / x
            abs(dz) < 1e-12 && return z - dz, x*(z - dz) - 1.0, true
            z = z - dz
            out = x*z - 1.0
        end
        return z, out, false
    end
    ir, _ = only(code_ircode(newton, Tuple{Float64, Float64}))
    l = latch_of(ir)
    back = filter(e -> e.sr === 1, l.edges)
    exits = filter(e -> e.sr === 0, l.edges)
    @test length(back) == 1 && length(exits) == 3
    @test all(e -> all(isundef, e.escapes), back)
    @test all(e -> any(!isundef, e.escapes), exits)
    # Each exit feeds only the two values its own return reads: z/out, z/dz, and
    # the updated z/out on the normal exit.
    @test all(e -> count(!isundef, e.escapes) == 2, exits)
    sci, _ = code_structured(newton, Tuple{Float64, Float64}) |> only
    for (x, z) in ((2.0, 1.0), (2.0, 0.5), (1e-9, 1e10), (0.0, Inf), (3.0, 1e8))
        @test isequal(execute(sci, x, z), newton(x, z))
    end

    # Two back edges (B5→B2, B6→B2) and two exits: B2→B3 returns `i+1` (%3),
    # bottom-tested B6→B7 returns `(i+1)^2` (%11). Julia source merges `continue`
    # paths into one back edge, so this is built by hand.
    two_back_ir() = build_ir([
        (stmts=[(GotoNode(2), Any)], succs=[2]),                                   # B1
        (stmts=[(PhiNode(Int32[1, 5, 6], Any[0, SSAValue(3), SSAValue(3)]), Int),   # B2: i
                (Expr(:call, Core.Intrinsics.add_int, SSAValue(2), 1), Int),        #  %3 = i+1
                (Expr(:call, Core.Intrinsics.slt_int, Argument(2), SSAValue(3)), Bool),
                (GotoIfNot(SSAValue(4), 4), Any)],                  succs=[4, 3]),
        (stmts=[(ReturnNode(SSAValue(3)), Any)],                    succs=Int[]),  # B3
        (stmts=[(Expr(:call, Core.Intrinsics.and_int, SSAValue(3), 1), Int),        # B4
                (Expr(:call, Core.:(===), SSAValue(7), 0), Bool),
                (GotoIfNot(SSAValue(8), 6), Any)],                  succs=[6, 5]),
        (stmts=[(GotoNode(2), Any)],                                succs=[2]),    # B5
        (stmts=[(Expr(:call, Core.Intrinsics.mul_int, SSAValue(3), SSAValue(3)), Int),  # B6
                (Expr(:call, Core.Intrinsics.slt_int, Argument(3), SSAValue(11)), Bool),
                (GotoIfNot(SSAValue(12), 2), Any)],                 succs=[2, 7]),
        (stmts=[(ReturnNode(SSAValue(11)), Any)],                   succs=Int[]),  # B7
    ], Any[Any, Int, Int])
    function two_back_ref(n, m)
        i = 0
        while true
            i += 1
            n < i && return i
            isodd(i) && m < i*i && return i*i
        end
    end
    l = latch_of(two_back_ir())
    back = filter(e -> e.sr === 1, l.edges)
    @test sort([e.src for e in back]) == [5, 6]
    @test all(e -> all(isundef, e.escapes), back)
    exits = filter(e -> e.sr === 0, l.edges)
    @test all(e -> any(!isundef, e.escapes), exits)
    # %3 dominates the bottom-tested exit B6→B7, but B7 only reads %11.
    @test all(e -> count(!isundef, e.escapes) == 1, exits)
    sci = StructuredIRCode(two_back_ir())
    for n in (0, 1, 4, 10), m in (0, 5, 30, 1000)
        @test execute(sci, n, m) == two_back_ref(n, m)
    end

    # Both exits read `i`, so both keep it.
    function both_use(v::Vector{Int}, n::Int)
        i = 0
        while true
            i += 1
            i > n && return i
            v[i] == 0 && return -i
        end
    end
    ir, _ = only(code_ircode(both_use, Tuple{Vector{Int}, Int}))
    exits = filter(e -> e.sr === 0, latch_of(ir).edges)
    @test length(exits) == 2
    @test all(e -> !isempty(e.escapes) && !any(isundef, e.escapes), exits)
    sci, _ = code_structured(both_use, Tuple{Vector{Int}, Int}) |> only
    for (v, n) in ((Int[1, 2, 3], 3), (Int[1, 0, 3], 3), (Int[0], 0), (Int[1, 2], 1))
        @test execute(sci, v, n) == both_use(v, n)
    end

    # The inner loop's exits continue into the outer loop body, which reads `s`
    # and `j` (directly, or through a block that does not read them itself).
    function nested(v::Vector{Int}, n::Int)
        s = 0
        for k in 1:n
            j = 0
            while true
                j += 1
                if j >= k
                    s += 1
                    break
                end
                v[j] < 0 && break
                s += 2
            end
            s += j
        end
        return s
    end
    ir, _ = only(code_ircode(nested, Tuple{Vector{Int}, Int}))
    keeps_all(l) = all(e -> e.sr !== 0 || !any(isundef, e.escapes), l.edges) &&
                   count(e -> e.sr === 0 && !isempty(e.escapes), l.edges) >= 2
    @test any(keeps_all, latch_edges(IRStructurizer.normalize_cf(ir)))
    sci, _ = code_structured(nested, Tuple{Vector{Int}, Int}) |> only
    for v in (Int[1, 2, 3, 4, 5], Int[1, -2, 3, -4, 5], Int[-1, -1, -1, -1, -1]), n in 0:5
        @test execute(sci, v, n) == nested(v, n)
    end
end

@testset "a carried value bound after the loop was entered" begin
    # The inner loop exits from its header and from a break; both exits feed one
    # phi, %13, right before the outer back edge. Once the inner loop's latch routes
    # both exits, that block has a single predecessor and the walk renames %13 to
    # the inner loop's result, after the outer loop collected %13 as a carried value.
    slt(a, b) = Expr(:call, Core.Intrinsics.slt_int, a, b)
    add(a, b) = Expr(:call, Core.Intrinsics.add_int, a, b)
    ir = build_ir([
        (stmts=[(GotoNode(2), Any)], succs=[2]),
        (stmts=[(PhiNode(Int32[1, 7], Any[0, SSAValue(13)]), Int), (slt(SSAValue(2), 3), Bool),
                (GotoIfNot(SSAValue(3), 8), Any)], succs=[3, 8]),
        (stmts=[(GotoNode(4), Any)], succs=[4]),
        (stmts=[(PhiNode(Int32[3, 6], Any[SSAValue(2), SSAValue(9)]), Int),
                (slt(SSAValue(6), 5), Bool), (GotoIfNot(SSAValue(7), 7), Any)], succs=[5, 7]),
        (stmts=[(add(SSAValue(6), 1), Int), (slt(SSAValue(9), Argument(2)), Bool),
                (GotoIfNot(SSAValue(10), 7), Any)], succs=[6, 7]),
        (stmts=[(GotoNode(4), Any)], succs=[4]),
        (stmts=[(PhiNode(Int32[4, 5], Any[SSAValue(6), SSAValue(9)]), Int),
                (GotoNode(2), Any)], succs=[2]),
        (stmts=[(ReturnNode(SSAValue(2)), Any)], succs=Int[]),
    ], Any[Any, Int])
    function expected(n)
        a = 0
        while a < 3
            b = a
            while true
                b < 5 || break
                c = b + 1
                if !(c < n)
                    b = c
                    break
                end
                b = c
            end
            a = b
        end
        a
    end
    for promote in (true, false)
        sci = StructuredIRCode(ir; promote)              # validates
        @test [execute(sci, n) for n in 0:6] == [expected(n) for n in 0:6]
    end
end

end  # regression suite
