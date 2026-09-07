using IRStructurizer: expand_for_loops!, IRValue, Undef, eachblock, resolve_line

# The exact expansion of ForOp (src/ir/expand.jl): the reference lowering of the
# counted-range contract, used by IRCode(::StructuredIRCode) and available to
# consumers without a native counted loop.

# Hand-built counted loops with a valid contract, compared with a mathematical
# reference over small integer domains. `entry` holds the ForOp at %4 and returns
# its first result. `body_builder(iv, carry)` fills the body and returns the
# continue values; the body may contain a nested conditional continuation.
function forop_sci(body_builder, lower, upper, step, T; inclusive, carry_init, carry_type=T,
                   argtypes=Any[Tuple{}])
    entry = Block()
    iv = BlockArgument(1, T)
    carry = BlockArgument(2, carry_type)
    body = Block()
    push!(body.args, carry)
    cont = body_builder(body, iv, carry)
    body.terminator = ContinueOp(IRValue[cont])
    op = ForOp(lower, upper, step, iv, body, IRValue[carry_init]; inclusive)
    push!(entry, 4, op, Tuple{carry_type})
    push!(entry, 5, Expr(:call, Core.getfield, SSAValue(4), 1), carry_type)
    entry.terminator = ReturnNode(SSAValue(5))
    sci = StructuredIRCode(argtypes, Any[], entry, 100)
    sci.max_arg_idx = 2
    return sci
end

# Mathematical reference: the visited values of the contract's range.
function visited(lower, upper, step; inclusive)
    T = typeof(lower)
    vals = T[]
    x = big(lower)
    while inclusive ? x <= big(upper) : x < big(upper)
        push!(vals, T(x))
        x += big(step)
    end
    return vals
end

@testset "expansion" begin

@testset "inclusive and exclusive ranges against the reference" begin
    # sum of the visited values, over every (lower, upper) pair of a narrow domain,
    # including the empty, singleton, full-width and typemax-ending ranges
    for T in (Int8, UInt8), step in (1, 3), inclusive in (true, false)
        st = T(step)
        domain = unique(T[typemin(T), typemin(T) + T(1), T(0), T(1), T(2), T(5), T(100),
                          typemax(T) - T(4), typemax(T) - T(1), typemax(T)])
        for lower in domain, upper in domain
            ref = visited(lower, upper, st; inclusive)
            # the contract: an inclusive end lies on the grid, an exclusive final
            # update is representable
            if inclusive
                lower <= upper && (big(upper) - big(lower)) % big(st) != 0 && continue
            else
                lower < upper && big(ref[end]) + big(st) > big(typemax(T)) && continue
            end
            sci = forop_sci(lower, upper, st, T; inclusive, carry_init=0, carry_type=Int) do body, iv, s
                push!(body, 1, Expr(:call, GlobalRef(Core, :zext_int), Int, iv), Int)
                push!(body, 2, Expr(:call, GlobalRef(Base, :add_int), s, SSAValue(1)), Int)
                SSAValue(2)
            end
            # `zext_int` sums the IV's bit pattern
            expected = sum(Int, reinterpret.(UInt8, ref); init=0)
            @test execute(sci) == expected
        end
    end
end

@testset "structure, results and anchors" begin
    count_range(a, b) = (s = 0; for i in a:b; s += 1; end; s)
    sci, _ = code_structured(count_range, Tuple{Int, Int}) |> only
    for_idx = only([idx for blk in eachblock(sci.entry) for (idx, e) in blk.body if e.stmt isa ForOp])
    loc = source_location(sci, for_idx)
    @test !isempty(loc)

    ex = expand_for_loops!(copy(sci))
    # the original is untouched, the copy has no ForOp and validates
    @test count_stmts(sci.entry, x -> x isa ForOp) == 1
    @test count_stmts(ex.entry, x -> x isa ForOp) == 0
    @test count_stmts(ex.entry, x -> x isa LoopOp) == 1
    validate_terminators(ex)
    validate_ssa_defs(ex)
    # the guard IfOp takes the ForOp's index and result type; the LoopOp inside it
    # carries the IV last and has only the public result
    guard = IRStructurizer.def(ex, SSAValue(for_idx))
    @test guard[:stmt] isa IfOp
    @test guard[:type] == Tuple{Int}
    loop = only(filter(x -> x isa LoopOp, collect(statements(guard[:stmt].then_region.body))))
    @test length(loop.init_values) == 2
    @test loop.body.args[end].type == Int
    # every synthesized statement (guard, loop, projection, ===, add_int, dispatch)
    # is anchored to the ForOp's source location
    synthesized = [idx for blk in eachblock(ex.entry) for (idx, _) in blk.body if idx > sci.max_ssa_idx]
    @test length(synthesized) >= 6
    for idx in synthesized
        @test source_location(ex, idx) == loc
    end
    # idempotent: nothing left to expand, and no re-promotion
    ex2 = expand_for_loops!(copy(ex))
    @test count_stmts(ex2.entry, x -> x isa LoopOp) == 1
    @test count_stmts(ex2.entry, x -> x isa ForOp) == 0
    for (a, b) in ((1, 5), (5, 1), (3, 3), (typemax(Int) - 1, typemax(Int)))
        @test execute(ex, a, b) == count_range(a, b)
    end

    # exclusive: a WhileOp keeps the index and type, the IV is the last carry
    counted(n) = (i = 0; s = 0; while i < n; s += i; i += 1; end; s)
    sci2, _ = code_structured(counted, Tuple{Int}) |> only
    for_idx2 = only([idx for blk in eachblock(sci2.entry) for (idx, e) in blk.body if e.stmt isa ForOp])
    ex2 = expand_for_loops!(copy(sci2))
    w = IRStructurizer.def(ex2, SSAValue(for_idx2))
    @test w[:stmt] isa WhileOp
    @test w[:type] == Tuple{Int}
    @test w[:stmt].before.args[end].type == Int
    @test count_stmts(ex2.entry, x -> x isa ForOp) == 0
    for idx in [idx for blk in eachblock(ex2.entry) for (idx, _) in blk.body if idx > sci2.max_ssa_idx]
        @test source_location(ex2, idx) == source_location(sci2, for_idx2)
    end
    for n in (-1, 0, 1, 5)
        @test execute(ex2, n) == counted(n)
    end
end

@testset "nested loops, carries, escaping IVs and empty paths" begin
    nested(n, m) = (s = 0; for i in 1:n; for j in 1:m; s += i * j; end; end; s)
    sci, _ = code_structured(nested, Tuple{Int, Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 2
    ex = expand_for_loops!(copy(sci))
    @test count_stmts(ex.entry, x -> x isa ForOp) == 0
    @test count_stmts(ex.entry, x -> x isa LoopOp) == 2
    for (n, m) in ((0, 3), (3, 0), (3, 4), (1, 1))
        @test execute(ex, n, m) == nested(n, m)
    end
    # an escaping IV rides as a kept carry: the last visited value, or the init
    last_iv(a, b) = (local i = zero(a); for j in a:b; i = j; end; i)
    for (a, b) in ((0x00, 0xff), (0xff, 0x00), (typemax(Int) - 2, typemax(Int)))
        @test @roundtrip last_iv(a, b)
    end
    # a `while`'s escaping IV reads back post-increment
    counted(n) = (i = 0; while i < n; i += 1; end; i)
    for n in (-3, 0, 4)
        @test @roundtrip counted(n)
    end
end

@testset "nested conditional continuations" begin
    # A continuation inside an IfOp arm gets the same exit/update sequence as the
    # body's own, in both flavors, and its synthesized statements carry the loop's
    # anchor. Julia never produces this shape (`continue` is merged by the
    # structurizer), so it is built by hand.
    function build(inclusive)
        sci = forop_sci(1, Core.Argument(2), 1, Int; inclusive, carry_init=0,
                        argtypes=Any[Tuple{}, Int]) do body, iv, s
            then_b = Block()
            then_b.terminator = ContinueOp(IRValue[s])        # skip the add
            else_b = Block()
            else_b.terminator = YieldOp(IRValue[])
            push!(body, 1, Expr(:call, GlobalRef(Base, :slt_int), iv, 3), Bool)
            push!(body, 2, IfOp(SSAValue(1), then_b, else_b), Tuple{})
            push!(body, 3, Expr(:call, GlobalRef(Base, :add_int), s, iv), Int)
            SSAValue(3)
        end
        sci.line_map[4] = -1   # a direct anchor for the ForOp
        return sci
    end
    ref(n, inclusive) = (s = 0; for i in (inclusive ? (1:n) : (1:n-1)); i < 3 || (s += i); end; s)
    for inclusive in (true, false)
        sci = build(inclusive)
        validate_terminators(sci)
        ex = expand_for_loops!(copy(sci))
        @test count_stmts(ex.entry, x -> x isa ForOp) == 0
        # two continuation points, each with its own synthesized latch
        n_add = count_stmts(ex.entry, s -> iscall_to(s, :add_int))
        @test n_add == 3   # the body's own `s + i`, plus two IV increments
        @test count_stmts(ex.entry, s -> s isa IfOp) == (inclusive ? 4 : 1)
        for blk in eachblock(ex.entry), (idx, _) in blk.body
            idx > 100 || continue
            @test resolve_line(ex.line_map, idx) == 1
        end
        for n in -1:6
            @test execute(sci, n) == ref(n, inclusive)
        end
    end
end

@testset "invalid counted-loop contracts" begin
    build_invalid(lo, up, st; inclusive) = forop_sci(
        (body, iv, carry) -> carry, lo, up, st, Int8; inclusive, carry_init=Int8(0))
    for (lo, up, st, inclusive) in (
        (Int8(1), Int8(5), Int8(0), true),
        (Int8(1), Int8(5), Int8(-1), true),
        (Int8(1), Int8(4), Int8(2), true),
        (Int8(126), Int8(127), Int8(2), false),
        (1, Int8(5), Int8(1), true),
        (Int8(1), UInt8(5), Int8(1), true),
        (Int8(1), Int8(5), 1.0, true))
        sci = build_invalid(lo, up, st; inclusive)
        @test_throws ErrorException validate_terminators(sci)
        @test_throws ErrorException expand_for_loops!(sci)
        @test count_stmts(sci.entry, x -> x isa ForOp) == 1
    end
    # Inferred constants carry the same obligations as literal operands.
    sci = build_invalid(Int8(1), Int8(4), Int8(2); inclusive=true)
    push!(sci.entry, 6, Int8(4), Core.Const(Int8(4)))
    sci.entry.body[4].stmt.upper = SSAValue(6)
    @test_throws ErrorException validate_terminators(sci)
end

@testset "validation of the expanded IR" begin
    # a loop-carried Undef init (an extra exit value) survives the expansion
    forlast(n) = (last = 0; for i in 1:n; last = i; end; last)
    sci, _ = code_structured(forlast, Tuple{Int}) |> only
    ex = expand_for_loops!(copy(sci))
    validate_terminators(ex)
    validate_ssa_defs(ex)
    for n in (-3, 0, 1, 5)
        @test execute(ex, n) == forlast(n)
    end
    # an unsupported IV type is refused
    entry = Block()
    iv = BlockArgument(1, Float64)
    body = Block()
    body.terminator = ContinueOp(IRValue[])
    push!(entry, 1, ForOp(1.0, 10.0, 1.0, iv, body, IRValue[]), Tuple{})
    entry.terminator = ReturnNode(nothing)
    bad = StructuredIRCode(Any[Tuple{}], Any[], entry, 1)
    @test_throws ErrorException expand_for_loops!(bad)
end

end  # expansion
