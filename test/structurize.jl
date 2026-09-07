#=============================================================================
 CFG Analysis Tests
 Tests that control flow regions are correctly identified.
=============================================================================#

@testset "CFG analysis" begin

@testset "acyclic regions" begin

@testset "block sequence" begin
    # Simple function: single addition (no control flow)
    @test @filecheck begin
        @check_not "if"
        code_structured(Tuple{Int}) do x
            @check "add_int"
            @check "return"
            x + 1
        end
    end
    @test @roundtrip (x -> x + 1)(5)

    # Multiple operations: (x + y) * (x - y)
    @test @filecheck begin
        @check_not "if"
        code_structured(Tuple{Int, Int}) do x, y
            @check "add_int"
            @check "sub_int"
            @check "mul_int"
            @check "return"
            (x + y) * (x - y)
        end
    end
    @test @roundtrip ((x, y) -> (x + y) * (x - y))(3, 2)
end

@testset "if-then-else: diamond pattern" begin
    # Both branches converge (diamond CFG pattern)
    @test @filecheck begin
        code_structured(Tuple{Int}) do x::Int
            @check "slt_int"
            @check "if"
            @check "add_int"
            @check "else"
            @check "sub_int"
            @check "return"
            x > 0 ? x + 1 : x - 1
        end
    end
    @test @roundtrip (x -> x > 0 ? x + 1 : x - 1)(5)
    @test @roundtrip (x -> x > 0 ? x + 1 : x - 1)(-3)
end

@testset "if-then-else: bool condition (no comparison)" begin
    # Bool condition directly, no comparison needed
    @test @filecheck begin
        code_structured(Tuple{Bool}) do x::Bool
            @check "if"
            @check "return 1"
            @check "else"
            @check "return 2"
            x ? 1 : 2
        end
    end
    @test @roundtrip (x -> x ? 1 : 2)(true)
    @test @roundtrip (x -> x ? 1 : 2)(false)
end

@testset "if-then-else: with comparison" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do x::Int
            @check "slt_int"
            @check "if"
            @check "return"
            @check "else"
            @check "neg_int"
            @check "return"
            x > 0 ? x : -x
        end
    end
end

@testset "termination: early return pattern" begin
    # One branch returns early, other continues
    @test @filecheck begin
        code_structured(Tuple{Int, Int}) do x::Int, y::Int
            @check "if"
            if x > y
                @check "mul_int"
                @check "return"
                return y * x
            end
            @check "else"
            @check "sub_int"
            @check "return"
            y - x
        end
    end
    f_early = (x::Int, y::Int) -> (x > y ? (return y * x) : nothing; y - x)
    @test @roundtrip f_early(5, 3)
    @test @roundtrip f_early(3, 5)
end

end  # acyclic regions

@testset "cyclic regions" begin

@testset "simple loop structure - escaping IV is a kept-carry ForOp" begin
    # `i=0; while i<n; i+=1; return i` reads the IV after the loop. A ForOp can't
    # carry the IV as a range result, but it can keep it as an ordinary carried
    # value, so the post-loop read is a normal result, correct for both the empty
    # case (= init 0) and non-empty (= n). Dropping it and aliasing the read to the
    # bound would miscompile the empty case.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            @check "for"
            i = 0
            while i < n
                i += 1
            end
            return i
        end
    end
    f_count = (n::Int) -> (i = 0; while i < n; i += 1; end; i)
    @test @roundtrip f_count(5)
    @test @roundtrip f_count(0)
    @test @roundtrip f_count(-3)   # empty by negative bound → init (0), not the bound
end

@testset "loop with condition" begin
    # Loop with condition check at header (empty body - self-loop pattern)
    @test @filecheck begin
        code_structured(Tuple{Int}) do flag::Int
            @check "while"
            while flag != 0
                @check "not_int"
                # spin
            end
            return flag
        end
    end
    # Only test with 0 (non-zero would spin forever)
    @test @roundtrip ((flag::Int) -> (while flag != 0; end; flag))(0)
end

@testset "loop with body statements" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            @check "while"
            @check "slt_int"
            while n > 0
                @check "sub_int"
                n -= 1
            end
            return n
        end
    end
    @test @roundtrip ((n::Int) -> (while n > 0; n -= 1; end; n))(5)
    @test @roundtrip ((n::Int) -> (while n > 0; n -= 1; end; n))(0)
end

@testset "nested loops" begin
    @test @filecheck begin
        code_structured(Tuple{Int, Int}) do n::Int, m::Int
            acc = 0
            i = 0
            @check "for %{{.*}} ="
            while i < n
                j = 0
                @check "for %{{.*}} ="
                while j < m
                    acc += 1
                    j += 1
                end
                i += 1
            end
            return acc
        end
    end
    f_nest = (n::Int, m::Int) -> (acc=0; i=0; while i<n; j=0; while j<m; acc+=1; j+=1; end; i+=1; end; acc)
    @test @roundtrip f_nest(3, 4)
end

end  # cyclic regions

end  # CFG analysis

#=============================================================================
 Loop Classification Tests
 Tests that loops are correctly classified into ForOp, WhileOp, or LoopOp.
 ForOp is detected directly during CFG analysis for counting patterns.
=============================================================================#

# Opaque ranges keep field reads in the inlined iteration protocol.
@noinline opaque_oneto(n) = Base.OneTo(n)
@noinline opaque_range(a, b) = a:b
@noinline opaque_steprange(a, s, b) = a:s:b

struct SideRange; stop::Int; end
const SIDE_STOP_CALLS = Ref(0)
@noinline side_stop(r::SideRange) = (SIDE_STOP_CALLS[] += 1; r.stop)
Base.iterate(r::SideRange) = r.stop < 1 ? nothing : (1, 1)
Base.iterate(r::SideRange, i::Int) = i === side_stop(r) ? nothing : (i + 1, i + 1)

mutable struct MutStop; stop::Int; end
@noinline opaque_mutstop(n) = MutStop(n)

# A body that records its visits and throws after a bounded number of them, so a
# loop that natively wraps around (or never terminates) can be observed without
# hanging and without the compiler folding the visits away.
const VISITS = Any[]
@noinline function visit!(i)
    push!(VISITS, i)
    length(VISITS) >= 4 && error("too many visits")
    return nothing
end

# A custom iterator with the unit-range protocol shape whose state wraps: it starts
# at 0xfe and stops on equality with 0x00, so it visits fe, ff, 00.
struct WrapIter end
Base.iterate(::WrapIter) = (0xfe, 0xfe)
Base.iterate(::WrapIter, s::UInt8) = s == 0x00 ? nothing : (s + 0x01, s + 0x01)

# A `while` whose header does more than compare: the call lands in the WhileOp's
# `before` region, which a ForOp has no place for.
const HEADER_CALLS = Ref(0)
@noinline header_bump!() = (HEADER_CALLS[] += 1; nothing)
side_header(n) = (i = 1; s = 0; while (header_bump!(); i <= n); s += i; i += 1; end; s)

@testset "loop classification" begin

@testset "ForOp detection" begin

@testset "bounded counter with escaping IV is a kept-carry ForOp" begin
    # The induction variable `i` is returned, so the ForOp keeps it as an ordinary
    # carried value instead of dropping it. The range still drives iteration (lower
    # 0, upper n, step 1) while the kept carry exposes the post-loop value, correct
    # for the empty case (= init 0) too. Dropping it and aliasing the read to the
    # bound would miscompile the empty case.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            @check "for"
            i = 0
            while i < n
                i += 1
            end
            return i
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        while i < n
            i += 1
        end
        return i
    end |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 1
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 0

    for_op = only(filter(x -> x isa ForOp, collect(statements(sci.entry.body))))
    @test for_op.lower == 0
    @test for_op.upper isa Core.Argument   # the bound `n`
    @test for_op.step == 1

    # Execution across empty (n ≤ 0 → init 0) and non-empty (→ n); the empty case
    # is what the buggy ForOp promotion got wrong (it returned the bound).
    counted(n) = (i = 0; while i < n; i += 1; end; i)
    for n in (-3, 0, 1, 5, 10)
        @test execute(sci, n) == counted(n)
    end
end

@testset "inclusive bound (<=) needs a bound below typemax" begin
    # `while i <= n` stops at `n` only because the update `n + 1` fails the test,
    # which wraps when `n == typemax`. A dynamic `n` supplies no proof, so the loop
    # keeps its own semantics as a WhileOp and no `n + 1` is synthesized either.
    # (Missing proof: `n < typemax(Int)`.)
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            i = 0
            acc = 0
            @check_not "add_int(_2, 1)"
            @check "while"
            @check "sle_int"
            @check_not "for"
            while i <= n
                acc += i
                i += 1
            end
            return acc
        end
    end
    f_incl = (n::Int) -> (i=0; acc=0; while i<=n; acc+=i; i+=1; end; acc)
    @test @roundtrip f_incl(5)
    @test @roundtrip f_incl(0)
    # A constant bound below typemax is that proof: the loop becomes an inclusive
    # ForOp, printed as the Julia range `0:1:100`.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            i = 0
            acc = 0
            @check "for %arg{{[0-9]+}} = 0:1:100"
            while i <= 100
                acc += i * n
                i += 1
            end
            return acc
        end
    end
    f_const = (n::Int) -> (i=0; acc=0; while i<=100; acc+=i*n; i+=1; end; acc)
    @test @roundtrip f_const(3)
    # `<` is the exclusive ForOp's own test (printed `0:1:<n`): with a unit step the
    # update `i + 1 <= n` always fits.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            i = 0
            acc = 0
            @check "for %arg{{[0-9]+}} = 0:1:<_2"
            while i < n
                acc += i
                i += 1
            end
            return acc
        end
    end
end

@testset "bounds at the edge of the integer type" begin
    # Neither promoter computes `bound ± step`: an exclusive `last + step` wrapped
    # for a range ending at `typemax` (or in any narrow type) and lost the loop.
    # The inclusive ForOp visits `last` itself, tested before the IV is advanced.
    count_range(a, b) = (s = 0; for i in a:b; s += 1; end; s)
    sum_range(a, b) = (s = zero(a); for i in a:b; s += i; end; s)
    for (a, b) in ((typemax(Int) - 1, typemax(Int)), (typemax(Int), typemax(Int)),
                   (0x00, 0xff), (0x70, 0x90), (Int8(120), Int8(127)),
                   (typemin(Int8), typemax(Int8)), (typemax(Int), typemax(Int) - 1))
        sci, _ = code_structured(count_range, Tuple{typeof(a), typeof(b)}) |> only
        @test count_stmts(sci.entry, x -> x isa ForOp) == 1
        @test @roundtrip count_range(a, b)
        @test @roundtrip sum_range(a, b)
    end
    # `last` of a stepped range is on the grid but may still be `typemax`. With
    # dynamic endpoints the alignment of `last` to the step is computed by the
    # inlined `steprange_last`, which the prover does not follow, so the loop stays
    # general and still iterates exactly. (Missing proof: `(last - a) % 2 == 0`.)
    count_step(a, b) = (s = 0; for i in a:Int8(2):b; s += 1; end; s)
    sci, _ = code_structured(count_step, Tuple{Int8, Int8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test @roundtrip count_step(Int8(1), Int8(127))
    @test @roundtrip count_step(Int8(1), Int8(100))
    @test @roundtrip count_step(Int8(1), Int8(0))
    # An escaping IV still reads back the last visited value.
    last_iv(a, b) = (local i; for j in a:b; i = j; end; i)
    @test @roundtrip last_iv(typemax(Int) - 2, typemax(Int))
    @test @roundtrip last_iv(0x00, 0xff)

    # Counting `while` loops compare by the IV's signedness (`ult_int`/`ule_int` were
    # lowered as signed compares before, so UInt8 loops crossing 0x80 exited early).
    # `<` with a unit step promotes: its update stays at or below the bound. `<=`
    # over a dynamic bound stays a WhileOp, wraparound included. (Missing proof:
    # `n < typemax(UInt8)`.)
    count_lt(a, n) = (i = a; s = 0; while i < n; s += 1; i += one(i); end; s)
    count_le(a, n) = (i = a; s = 0; while i <= n; s += 1; i += one(i); end; s)
    sci, _ = code_structured(count_lt, Tuple{UInt8, UInt8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 1
    sci, _ = code_structured(count_le, Tuple{UInt8, UInt8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 1
    for f in (count_lt, count_le)
        @test @roundtrip f(0x70, 0x90)
        @test @roundtrip f(0x90, 0x70)
        @test @roundtrip f(0x00, 0xfe)
    end
    @test @roundtrip count_lt(typemax(Int) - 2, typemax(Int))
    @test @roundtrip count_le(typemax(Int) - 2, typemax(Int) - 1)
    @test @roundtrip count_le(Int8(120), Int8(126))

    # `<=` with a non-unit step and a dynamic bound may never land on the bound, so
    # it stays a WhileOp. (Missing proof: `n` on the grid of `0:2` and `n + 2` fits.)
    count_le2(n) = (i = 0; s = 0; while i <= n; s += 1; i += 2; end; s)
    sci, _ = code_structured(count_le2, Tuple{Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 1
    @test @roundtrip count_le2(5)
    @test @roundtrip count_le2(4)
    @test @roundtrip count_le2(-1)
end

@testset "promotion requires a counted-loop proof" begin
    # The counted-range contract (see the `ForOp` docstring) excludes wraparound, so
    # a source loop becomes a ForOp only when its entry order, endpoint reachability
    # and final update are proved. A recognizable shape alone is not a proof.

    # `while i <= n` over UInt8 entered with n = typemax: the increment wraps and
    # the native loop visits fe, ff, 00, 01, ... until the body throws. An inclusive
    # ForOp would stop on equality with n and return after ff. Without a constant
    # bound proving `n < typemax`, the loop stays a WhileOp, wraparound included.
    le_wrap(i::UInt8, n::UInt8) = (while i <= n; visit!(i); i += 0x01; end; i)
    empty!(VISITS)
    @test_throws ErrorException le_wrap(0xfe, 0xff)
    native = copy(VISITS)
    @test native == [0xfe, 0xff, 0x00, 0x01]
    sci, _ = code_structured(le_wrap, Tuple{UInt8, UInt8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 1
    empty!(VISITS)
    @test_throws ErrorException execute(sci, 0xfe, 0xff)
    @test VISITS == native

    # The iteration protocol of a custom iterator has the unit-range shape (equality
    # exit before the increment) but no guard establishing `first <= last`: the
    # state starts above its stop value and wraps. Promotion would add a
    # `lower <= upper` entry guard and skip the whole loop; it must stay a LoopOp.
    wrap_visits() = (for i in WrapIter(); visit!(i); end; nothing)
    empty!(VISITS)
    wrap_visits()
    native2 = copy(VISITS)
    @test native2 == [0xfe, 0xff, 0x00]
    sci2, _ = code_structured(wrap_visits, Tuple{}) |> only
    @test count_stmts(sci2.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci2.entry, x -> x isa LoopOp) == 1
    empty!(VISITS)
    execute(sci2)
    @test VISITS == native2
end

# Julia's inlined unit-range `iterate`, as a hand-built CFG: the shape both 1.11
# and 1.12 lower `for i in first:upper` to, with the entry guard and the in-loop
# exit protocol (a branch yielding `(next, done)`, its projections, `not_int`, the
# exit branch), the loop taken on the flag's false path in either branch polarity.
# `bound` selects the endpoint the loop's equality exit compares against (argument
# 3, the guard's, or an unrelated 4th argument); `cmp` is the guard's order test.
# The loop counts its iterations.
function unit_range_guard_ir(; bound::Int=3, cmp::Symbol=:slt_int, inverted::Bool=false)
    guard = [(stmts=[(Expr(:call, GlobalRef(Base, cmp), Argument(3), Argument(2)), Bool),
                     (GotoIfNot(SSAValue(1), 3), Any)], succs=[2, 3]),    # %1 = upper < first
             (stmts=[(GotoNode(4), Any)], succs=[4]),                      # done: flag true
             (stmts=[(GotoNode(4), Any)], succs=[4])]                      # not done: flag false, iv = first
    flag = (PhiNode(Int32[2, 3], Any[true, false]), Bool)                  # %5
    iv0 = (PhiNode(Int32[3], Any[Argument(2)]), Int)                      # %6 (undef when done)
    # The loop, SSA %9-%23 in both layouts, header block `h`: header phis for iv
    # and the count; `iv === bound`; the done/next arms merge into `(next, done)`
    # phis; `not_int(done)` decides between the latch and the exit edge.
    next_phi = Vector{Any}(undef, 2); next_phi[2] = SSAValue(16)
    loop(h, merge) = [
        (stmts=[(PhiNode(Int32[4, h + 5], Any[SSAValue(6), SSAValue(18)]), Int),   # %9 iv
                (PhiNode(Int32[4, h + 5], Any[0, SSAValue(13)]), Int),             # %10 count
                (GotoNode(h + 1), Any)], succs=[h + 1]),
        (stmts=[(Expr(:call, GlobalRef(Core, :(===)), SSAValue(9), Argument(bound)), Bool),   # %12
                (Expr(:call, GlobalRef(Base, :add_int), SSAValue(10), 1), Int),               # %13
                (GotoIfNot(SSAValue(12), h + 3), Any)], succs=[h + 2, h + 3]),
        (stmts=[(GotoNode(h + 4), Any)], succs=[h + 4]),                                       # done arm
        (stmts=[(Expr(:call, GlobalRef(Base, :add_int), SSAValue(9), 1), Int),                # %16 next
                (GotoNode(h + 4), Any)], succs=[h + 4]),
        (stmts=[(PhiNode(Int32[h + 2, h + 3], next_phi), Int),                                 # %18
                (PhiNode(Int32[h + 2, h + 3], Any[true, false]), Bool),                        # %19
                (Expr(:call, GlobalRef(Base, :not_int), SSAValue(19)), Bool),                  # %20
                (GotoIfNot(SSAValue(20), h + 6), Any)], succs=[h + 5, h + 6]),
        (stmts=[(GotoNode(h), Any)], succs=[h]),                                               # latch
        (stmts=[(GotoNode(merge), Any)], succs=[merge]),                                       # exit edge
    ]
    exit_path(merge) = (stmts=[(GotoNode(merge), Any)], succs=[merge])
    if inverted
        # `if flag`: true falls through to the exit path (BB5), false → the loop (BB6)
        blocks = vcat(guard,
            [(stmts=[flag, iv0, (GotoIfNot(SSAValue(5), 6), Any)], succs=[5, 6]),
             exit_path(13)],
            loop(6, 13),
            [(stmts=[(PhiNode(Int32[5, 12], Any[0, SSAValue(13)]), Int),
                     (ReturnNode(SSAValue(24)), Any)], succs=Int[])])
    else
        # `if not_int(flag)` (Julia's shape): true falls through to the loop (BB5),
        # false → the exit path (BB12)
        blocks = vcat(guard,
            [(stmts=[flag, iv0, (Expr(:call, GlobalRef(Base, :not_int), SSAValue(5)), Bool),
                     (GotoIfNot(SSAValue(7), 12), Any)], succs=[5, 12])],
            loop(5, 13),
            [exit_path(13),
             (stmts=[(PhiNode(Int32[11, 12], Any[SSAValue(13), 0]), Int),
                     (ReturnNode(SSAValue(25)), Any)], succs=Int[])])
    end
    return build_ir(blocks, Any[Any, Int, Int, Int])
end

@testset "counted-loop proofs: acceptance and rejection" begin
    # --- the unit-range entry guard, hand-built for both polarities ---
    count_ref(first, upper) = length(first:upper)
    for inverted in (false, true)
        ir = unit_range_guard_ir(; inverted)
        CC.verify_ir(ir)
        sci = StructuredIRCode(ir)
        @test count_stmts(sci.entry, x -> x isa ForOp) == 1
        for (a, b) in ((1, 5), (5, 1), (3, 3), (typemax(Int) - 1, typemax(Int)))
            @test execute(sci, a, b, b) == count_ref(a, b)
        end
    end
    # The equality exit compares against a value the guard never ordered: no proof.
    sci = StructuredIRCode(unit_range_guard_ir(; bound=4))
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa LoopOp) == 1
    @test execute(sci, 1, 5, 5) == 5
    # The guard's order test has the wrong signedness for the IV type: no proof.
    sci = StructuredIRCode(unit_range_guard_ir(; cmp=:ult_int))
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test execute(sci, 1, 5, 5) == 5

    # --- a header-tested loop whose predicate does not match the IV type ---
    # `while ult_int(i, n)` over Int: Julia never emits it, but the ForOp's own
    # signed compare would reinterpret it, so it stays a WhileOp.
    function lt_ir(cmp::Symbol)
        build_ir([
            (stmts=[(GotoNode(2), Any)], succs=[2]),
            (stmts=[(PhiNode(Int32[1, 3], Any[0, SSAValue(5)]), Int),
                    (Expr(:call, GlobalRef(Base, cmp), SSAValue(2), Argument(2)), Bool),
                    (GotoIfNot(SSAValue(3), 4), Any)], succs=[3, 4]),
            (stmts=[(Expr(:call, GlobalRef(Base, :add_int), SSAValue(2), 1), Int),
                    (GotoNode(2), Any)], succs=[2]),
            (stmts=[(ReturnNode(SSAValue(2)), Any)], succs=Int[]),
        ], Any[Any, Int])
    end
    sci = StructuredIRCode(lt_ir(:slt_int))
    @test count_stmts(sci.entry, x -> x isa ForOp) == 1
    sci = StructuredIRCode(lt_ir(:ult_int))
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 1
    for n in (0, 5)
        @test execute(sci, n) == n
    end

    # --- steps: zero, negative and unknown-sign steps are not counted loops ---
    zero_step(i::UInt8, n::UInt8) = (while i < n; visit!(i); i += 0x00; end; i)
    empty!(VISITS)
    @test_throws ErrorException zero_step(0x01, 0x05)
    native = copy(VISITS)
    @test native == [0x01, 0x01, 0x01, 0x01]
    sci, _ = code_structured(zero_step, Tuple{UInt8, UInt8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    empty!(VISITS)
    @test_throws ErrorException execute(sci, 0x01, 0x05)
    @test VISITS == native
    neg_step(n) = (i = 10; s = 0; while i < n; s += i; i += -1; end; s)   # never terminates for n > 10
    sci, _ = code_structured(neg_step, Tuple{Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test @roundtrip neg_step(5)

    # --- exclusive loops whose final update can wrap ---
    # `i < n` with step 2 over Int8, entered at 126 with n = 127: natively the
    # update wraps to -128 and the loop goes on until the body throws. A dynamic
    # bound has no representability proof (missing: `n + 1 <= typemax(Int8)`).
    lt2(i::Int8, n::Int8) = (while i < n; visit!(i); i += Int8(2); end; i)
    empty!(VISITS)
    @test_throws ErrorException lt2(Int8(126), Int8(127))
    native = copy(VISITS)
    @test native == Int8[126, -128, -126, -124]
    sci, _ = code_structured(lt2, Tuple{Int8, Int8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 1
    empty!(VISITS)
    @test_throws ErrorException execute(sci, Int8(126), Int8(127))
    @test VISITS == native
    # A constant bound decides it: 127 + 2 - 1 does not fit, 126 + 2 - 1 does.
    lt2_bad(i::Int8) = (while i < Int8(127); visit!(i); i += Int8(2); end; i)
    lt2_ok(i::Int8) = (while i < Int8(126); visit!(i); i += Int8(2); end; i)
    sci, _ = code_structured(lt2_bad, Tuple{Int8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    empty!(VISITS)
    @test_throws ErrorException execute(sci, Int8(126))
    @test VISITS == native
    sci, _ = code_structured(lt2_ok, Tuple{Int8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 1
    @test !only(filter(x -> x isa ForOp, collect(statements(sci.entry.body)))).inclusive
    for a in (Int8(120), Int8(125), Int8(126), Int8(127))
        empty!(VISITS); expected = lt2_ok(a); native = copy(VISITS)
        empty!(VISITS)
        @test execute(sci, a) == expected
        @test VISITS == native
    end

    # --- inclusive loops with a larger step: alignment and the final update ---
    le3_aligned(x) = (i = Int8(1); s = 0; while i <= Int8(10); s += i * x; i += Int8(3); end; s)
    le3_offgrid(x) = (i = Int8(1); s = 0; while i <= Int8(11); s += i * x; i += Int8(3); end; s)
    le3_wrap(x::Int8) = (i = Int8(1); while i <= Int8(127); visit!(i); i += Int8(3); end; i)
    sci, _ = code_structured(le3_aligned, Tuple{Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 1
    @test only(filter(x -> x isa ForOp, collect(statements(sci.entry.body)))).inclusive
    @test @roundtrip le3_aligned(2)
    sci, _ = code_structured(le3_offgrid, Tuple{Int}) |> only   # 11 is off the grid of 1:3
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test @roundtrip le3_offgrid(2)
    # 127 is on the grid, but the exiting update 127 + 3 wraps: natively the loop
    # runs on (1, 4, 7, 10, ... until the body throws), so it stays a WhileOp.
    empty!(VISITS)
    @test_throws ErrorException le3_wrap(Int8(0))
    native = copy(VISITS)
    sci, _ = code_structured(le3_wrap, Tuple{Int8}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    empty!(VISITS)
    @test_throws ErrorException execute(sci, Int8(0))
    @test VISITS == native

    # --- required positive cases: dynamic unit ranges with their entry proof ---
    count_range(a, b) = (s = 0; for i in a:b; s += 1; end; s)
    sum_opaque(a, b) = (s = 0; for i in opaque_range(a, b); s += i; end; s)
    sum_arg(r::UnitRange{Int}) = (s = 0; for i in r; s += i; end; s)
    nested_dep(n) = (s = 0; for i in 1:n; for j in 1:i; s += i * j; end; end; s)
    in_if(b::Bool, n) = (s = 0; if b; for i in 1:n; s += i; end; end; s)
    for (f, tt, nfor) in ((count_range, Tuple{Int, Int}, 1), (count_range, Tuple{UInt8, UInt8}, 1),
                          (sum_opaque, Tuple{Int, Int}, 1), (sum_arg, Tuple{UnitRange{Int}}, 1),
                          (nested_dep, Tuple{Int}, 2), (in_if, Tuple{Bool, Int}, 1))
        sci, _ = code_structured(f, tt) |> only
        @test count_stmts(sci.entry, x -> x isa ForOp) == nfor
        @test count_stmts(sci.entry, x -> x isa WhileOp || x isa LoopOp) == 0
        for blk in IRStructurizer.eachblock(sci.entry), (_, e) in blk.body
            e.stmt isa ForOp && @test e.stmt.inclusive
        end
    end
    @test @roundtrip count_range(0x10, 0x20)
    @test @roundtrip sum_opaque(2, 5)
    @test @roundtrip sum_opaque(5, 2)
    @test @roundtrip sum_arg(3:7)
    @test @roundtrip sum_arg(7:3)
    @test @roundtrip nested_dep(4)
    @test @roundtrip in_if(true, 4)
    @test @roundtrip in_if(false, 4)
end

@testset "inclusive bound with Core.Const upper type" begin
    # An inferred constant is a valid proof input: the `Core.Const(Int32(10))` type
    # of the bound SSA value proves `upper < typemax(Int32)`, so the `<=` loop still
    # promotes to an inclusive ForOp although its bound is not a literal.
    function const_upper(n::Int32)
        i = Int32(0)
        acc = Int32(0)
        upper = n + Int32(0)
        while i <= upper
            acc += i
            i += Int32(1)
        end
        return acc
    end
    ir, _ = only(code_ircode(const_upper, (Int32,)))
    # Patch the upper bound SSA type to Core.Const (simulates custom interpreters
    # that infer constant return types without folding)
    ir.stmts.type[1] = Core.Const(Int32(10))
    sci = StructuredIRCode(ir)
    for_ops = filter(x -> x isa ForOp, collect(statements(sci.entry.body)))
    @test length(for_ops) == 1
end

@testset "bounded counter with accumulator" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            i = 0
            acc = 0
            @check "for %{{.*}} ="
            while i < n
                @check "add_int"
                acc += i
                i += 1
            end
            @check "continue"
            return acc
        end
    end

    # Verify block args and init_values (FileCheck can't check these)
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        acc = 0
        while i < n
            acc += i
            i += 1
        end
        return acc
    end |> only
    for_ops = filter(x -> x isa ForOp, collect(statements(sci.entry.body)))
    @test length(for_ops) == 1

    for_op = for_ops[1]
    @test length(for_op.body.args) == 1
    @test length(for_op.init_values) == 1

    f_acc = (n::Int) -> (i=0; acc=0; while i<n; acc+=i; i+=1; end; acc)
    @test @roundtrip f_acc(5)
    @test @roundtrip f_acc(0)
end

@testset "Julia for-in-range (1:n) produces ForOp" begin
    # Native for-in-range iterator protocol is recognized and promoted to ForOp.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            acc = 0
            @check "for"
            for i in 1:n
                @check "add_int"
                acc += i
            end
            return acc
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n::Int
        acc = 0
        for i in 1:n
            acc += i
        end
        return acc
    end |> only

    # Verify IR is valid
    @test sci isa StructuredIRCode

    f_forin = (n::Int) -> (acc=0; for i in 1:n; acc+=i; end; acc)
    @test @roundtrip f_forin(5)
    @test @roundtrip f_forin(0)
end

@testset "nested for loops" begin
    @test @filecheck begin
        code_structured(Tuple{Int, Int}) do n::Int, m::Int
            acc = 0
            i = 0
            @check "for"
            while i < n
                j = 0
                @check "for"
                while j < m
                    acc += 1
                    j += 1
                end
                i += 1
            end
            return acc
        end
    end
end

@testset "sequential while loops" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        # Loop 1: accumulate
        i = 0
        acc = 0
        while i < n
            acc += i
            i += 1
        end
        # Loop 2: uses result from loop 1
        j = 0
        result = 0
        while j < n
            result += acc
            j += 1
        end
        return result
    end |> only

    for_ops = filter(x -> x isa ForOp, collect(statements(sci.entry.body)))
    @test length(for_ops) == 2

    f_seq = (n::Int) -> (i=0; acc=0; while i<n; acc+=i; i+=1; end;
                         j=0; result=0; while j<n; result+=acc; j+=1; end; result)
    @test @roundtrip f_seq(5)
end

@testset "sequential for loops" begin
    sci, _ = code_structured(Tuple{Int32}) do n::Int32
        # Loop 1: accumulate
        acc = Int32(0)
        for i in Int32(1):n
            acc += i
        end
        # Loop 2: uses result from loop 1
        result = Int32(0)
        for j in Int32(1):n
            result += acc
        end
        return result
    end |> only

    all_stmts = collect(statements(sci.entry.body))
    function count_loops(stmts)
        n = 0
        for s in stmts
            if s isa LoopOp || s isa ForOp
                n += 1
            elseif s isa IfOp
                n += count_loops(collect(statements(s.then_region.body)))
                n += count_loops(collect(statements(s.else_region.body)))
            end
        end
        n
    end
    @test count_loops(all_stmts) == 2
end

@testset "sequential for loops with constant bounds" begin
    sci, _ = code_structured(Tuple{Vector{Float32}, Vector{Float32}, Vector{Float32}}) do a::Vector{Float32}, b::Vector{Float32}, c::Vector{Float32}
        acc = 0.0f0
        for i in Int32(1):Int32(2)
            acc += a[i]
        end
        for i in Int32(1):Int32(2)
            c[i] = b[i] + acc
        end
        return nothing
    end |> only

    all_stmts = collect(statements(sci.entry.body))
    function count_loops(stmts)
        n = 0
        for s in stmts
            if s isa LoopOp || s isa ForOp
                n += 1
            elseif s isa IfOp
                n += count_loops(collect(statements(s.then_region.body)))
                n += count_loops(collect(statements(s.else_region.body)))
            end
        end
        n
    end
    @test count_loops(all_stmts) == 2
end

@testset "opaque range: body-defined bound is hoisted ahead of the ForOp" begin
    # Hoist the repeated stop read ahead of the ForOp, which uses it as its
    # inclusive bound.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            s = 0
            @check "getfield({{%[0-9]+}}, :stop)"
            @check "[[STOP:%[0-9]+]] = Base.getfield({{%[0-9]+}}, :stop)"
            @check "= for {{.*}}:1:[[STOP]]"
            @check_not "getfield"
            for i in opaque_oneto(n)
                s += i * i
            end
            @check "continue"
            return s
        end
    end

    sum_oneto(n) = (s = 0; for i in opaque_oneto(n); s += i * i; end; s)
    @test @roundtrip sum_oneto(5)
    @test @roundtrip sum_oneto(1)
    @test @roundtrip sum_oneto(0)

    sum_range(a, b) = (s = 0; for i in opaque_range(a, b); s += i; end; s)
    @test @roundtrip sum_range(2, 5)
    @test @roundtrip sum_range(3, 3)
    @test @roundtrip sum_range(5, 2)   # empty

    # The iteration-protocol rewrite requires a known positive step.
    sum_steprange(n, st) = (s = 0; for i in opaque_steprange(1, st, n); s += i; end; s)
    sci, _ = code_structured(sum_steprange, Tuple{Int, Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test @roundtrip sum_steprange(10, 3)
    @test @roundtrip sum_steprange(10, 7)
    @test @roundtrip sum_steprange(0, 2)
    @test @roundtrip sum_steprange(-5, -2)   # 1, -1, -3, -5
    sum_inline_step(n, st) = (s = 0; for i in 1:st:n; s += i; end; s)
    sci, _ = code_structured(sum_inline_step, Tuple{Int, Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test @roundtrip sum_inline_step(-5, -2)
    @test @roundtrip sum_inline_step(10, 3)
    # A constant step with a dynamic bound: the inlined `steprange_last` computes
    # `last` on the grid, but the prover does not follow it, so the range stays a
    # general loop. (Missing proof: `(last - 1) % 2 == 0`.)
    sum_step2(n) = (s = 0; for i in 1:2:n; s += i; end; s)
    sci, _ = code_structured(sum_step2, Tuple{Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test @roundtrip sum_step2(10)
    @test @roundtrip sum_step2(0)

    # The WhileOp path drops the whole `before` region, so a header-computed bound
    # (`r.stop` on an opaque `r`) must be hoisted there too. `<` promotes; `<=`
    # stays a WhileOp, header and all. (Missing proof: `r.stop < typemax(Int)`.)
    while_le(n) = (r = opaque_oneto(n); i = 1; s = 0; while i <= r.stop; s += i; i += 1; end; s)
    while_lt(n) = (r = opaque_oneto(n); i = 1; s = 0; while i < r.stop; s += i; i += 1; end; s)
    sci, _ = code_structured(while_lt, Tuple{Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 1
    sci, _ = code_structured(while_le, Tuple{Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 1
    @test @roundtrip while_le(5)
    @test @roundtrip while_le(0)
    @test @roundtrip while_lt(5)
    @test @roundtrip while_lt(0)

    # A step read from an opaque object is a runtime value of unknown sign, so the
    # loop stays a WhileOp; nothing is speculated. (Missing proof: `r.step > 0`.)
    function while_step(n, st)
        r = opaque_steprange(1, st, n)
        i = 1
        s = 0
        while i < n
            s += i
            i += r.step
        end
        return s
    end
    sci, _ = only(code_structured(while_step, Tuple{Int, Int}))
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 1
    @test @roundtrip while_step(10, 3)
    @test @roundtrip while_step(1, 3)
    @test @roundtrip while_step(0, 3)
end

@testset "body-defined bound that is not loop-invariant is not promoted" begin
    # Each bound below is an SSA value defined inside the loop that cannot be hoisted:
    # the loop must stay a WhileOp/LoopOp (and validate) rather than become a ForOp.
    function stays_loop(f, T)
        sci, _ = code_structured(f, T) |> only
        return count_stmts(sci.entry, x -> x isa ForOp) == 0 &&
               count_stmts(sci.entry, x -> x isa WhileOp || x isa LoopOp) == 1
    end

    # Bound depends on the induction variable.
    bound_uses_iv(n) = (i = 1; s = 0; while i <= n - i; s += i; i += 1; end; s)
    @test stays_loop(bound_uses_iv, Tuple{Int})
    @test @roundtrip bound_uses_iv(10)
    @test @roundtrip bound_uses_iv(0)

    # Bound is a side-effecting non-inlined call (iteration-protocol path).
    sum_side(n) = (s = 0; for i in SideRange(n); s += i; end; s)
    @test stays_loop(sum_side, Tuple{Int})
    @test @roundtrip sum_side(5)
    @test @roundtrip sum_side(0)

    # Bound is read from a mutable object the body writes: the `getfield` is
    # effect-free and nothrow but not `:consistent`, so hoisting it would freeze the
    # bound and change the trip count.
    function shrinking(n)
        r = opaque_mutstop(n)
        i = 1; s = 0
        while i <= r.stop
            s += i; r.stop -= 1; i += 1
        end
        return s
    end
    @test stays_loop(shrinking, Tuple{Int})
    @test @roundtrip shrinking(5)
    @test @roundtrip shrinking(0)
end

@testset "while header with a side effect is not promoted" begin
    # The WhileOp-to-ForOp promotion drops the `before` region, so a header statement
    # that is neither the hoisted bound nor deletable must keep the loop a WhileOp.
    # Previously the call was silently dropped from the promoted ForOp.
    HEADER_CALLS[] = 0
    expected = side_header(3)
    native_calls = HEADER_CALLS[]
    @test native_calls == 4
    sci, _ = code_structured(side_header, Tuple{Int}) |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    @test count_stmts(sci.entry, x -> x isa WhileOp) == 1
    HEADER_CALLS[] = 0
    @test execute(sci, 3) == expected
    @test HEADER_CALLS[] == native_calls
end

@testset "while header values used by the body retain their scope" begin
    function header_value(n)
        i = 1
        s = 0
        while (k = n - i; i < n)
            s += k
            i += 1
        end
        return s
    end
    sci, _ = only(code_structured(header_value, Tuple{Int}))
    @test count_stmts(sci.entry, x -> x isa LoopOp) == 1
    @test count_stmts(sci.entry, x -> x isa ForOp || x isa WhileOp) == 0
    @test @roundtrip header_value(5)
    @test @roundtrip header_value(0)
end

@testset "hoisting requires safe speculation" begin
    # Only Julia 1.11 uses the builtin fallback when the termination bit is absent.
    CC = IRStructurizer.CC
    m = IRStructurizer.SSAMap()
    push!(m, (1, Expr(:call, GlobalRef(Core, :getfield), Core.Argument(2), QuoteNode(:stop)), Int, CC.IR_FLAG_NULL))
    push!(m, (2, Expr(:call, GlobalRef(Base, :add_int), Core.SSAValue(1), 1), Int, CC.IR_FLAG_NULL))
    push!(m, (3, Expr(:invoke, nothing, GlobalRef(Base, :sum), Core.Argument(2)), Int, CC.IR_FLAG_NULL))
    push!(m, (4, Expr(:invoke, nothing, GlobalRef(Base, :sum), Core.Argument(2)), Int, CC.IR_FLAG_TERMINATES))
    @test IRStructurizer.terminates(get(m, 1, nothing)) == (VERSION < v"1.12-")
    @test IRStructurizer.terminates(get(m, 2, nothing)) == (VERSION < v"1.12-")
    @test !IRStructurizer.terminates(get(m, 3, nothing))
    @test IRStructurizer.terminates(get(m, 4, nothing))
    # A statement with every required bit is hoistable regardless of what it calls.
    full = IRStructurizer.IR_FLAGS_HOISTABLE | CC.IR_FLAG_TERMINATES
    push!(m, (5, Expr(:invoke, nothing, GlobalRef(Base, :sum), Core.Argument(2)), Int, full))
    args, blk = IRStructurizer.BlockArgument[], IRStructurizer.Block()
    @test IRStructurizer.hoistable_loop_def(get(m, 5, nothing), args, blk)
    @test !IRStructurizer.hoistable_loop_def(get(m, 3, nothing), args, blk)
    # Hoisting speculates the statement on inputs it was never reached with, so a
    # statement that may be undefined behavior (`noub` unset) stays where it is even
    # when it is removable, consistent and terminating.
    push!(m, (6, Expr(:invoke, nothing, GlobalRef(Base, :sum), Core.Argument(2)), Int, full & ~CC.IR_FLAG_NOUB))
    @test !IRStructurizer.hoistable_loop_def(get(m, 6, nothing), args, blk)
    for f in (Core.Intrinsics.llvmcall, Core.Intrinsics.atomic_pointermodify)
        # These intrinsics can run arbitrary code, even with all other effects
        # promised by the caller. The fallback must not infer termination.
        push!(m, (7, Expr(:call, f), Int, full & ~CC.IR_FLAG_TERMINATES))
        @test !IRStructurizer.terminates(get(m, 7, nothing))
        @test !IRStructurizer.hoistable_loop_def(get(m, 7, nothing), args, blk)
    end
end

end  # ForOp detection

@testset "WhileOp detection" begin

@testset "condition-only spinloop" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do flag::Int
            @check "while"
            while flag != 0
                @check "not_int"
            end
            return flag
        end
    end
end

@testset "decrementing loop (non-ForOp pattern)" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            @check "while"
            @check "slt_int"
            while n > 0
                @check "sub_int"
                n -= 1
            end
            return n
        end
    end
end

end  # WhileOp detection

@testset "WhileOp/LoopOp fallback" begin

@testset "dynamic step" begin
    # Loop where step is modified inside loop body (not a valid ForOp)
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        step = 1
        while i < n
            i += step
            step += 1
        end
        return i
    end |> only
    @test sci isa StructuredIRCode

    # Should have some loop op (not ForOp since step changes)
    loop_ops = filter(x -> x isa ForOp || x isa WhileOp || x isa LoopOp, collect(statements(sci.entry.body)))
    @test length(loop_ops) >= 1
    # The step is a carried block argument, which a ForOp (whose step is evaluated
    # outside the body) cannot express.
    @test count_stmts(sci.entry, x -> x isa ForOp) == 0
    f_dyn = (n::Int) -> (i = 0; step = 1; while i < n; i += step; step += 1; end; i)
    @test @roundtrip f_dyn(10)
    @test @roundtrip f_dyn(0)
end

@testset "step defined inside loop body" begin
    # Regression test: when the step is an SSA value defined inside the loop body
    # (e.g., a non-inlinable call), ForOp detection must reject it because the step
    # reference would be undefined at the ForOp level.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            i = 0
            @check_not "for"
            @check "while"
            while i < n
                @check "getfield"
                @check "add_int"
                i += _STEP_REF[]
            end
            return i
        end
    end
end

end  # WhileOp/LoopOp fallback

end  # loop classification

#=============================================================================
 Nested Control Flow Tests
=============================================================================#

@testset "nested control flow" begin

@testset "if inside loop" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            acc = 0
            i = 0
            @check "for"
            while i < n
                @check "if"
                if i % 2 == 0
                    @check "add_int"
                    acc += i
                end
                i += 1
            end
            return acc
        end
    end
    f_ifinloop = (n::Int) -> (acc=0; i=0; while i<n; if i%2==0; acc+=i; end; i+=1; end; acc)
    @test @roundtrip f_ifinloop(6)
end

@testset "loop inside if" begin
    @test @filecheck begin
        code_structured(Tuple{Int, Int}) do x::Int, n::Int
            @check "if"
            if x > 0
                i = 0
                @check "for"
                while i < n
                    i += 1
                end
                return i
            @check "else"
            else
                @check "return 0"
                return 0
            end
        end
    end
end

end  # nested control flow

#=============================================================================
 Regression Tests
=============================================================================#

@testset "regression" begin

@testset "no duplicated statements after loop" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do x::Int
            i = 0
            @check "for"
            while i < x
                i += 1
            end
            # This should appear exactly once
            @check "mul_int"
            result = i * 2
            @check_not "mul_int"
            @check "return"
            return result
        end
    end
    f_dup = (x::Int) -> (i=0; while i<x; i+=1; end; i*2)
    @test @roundtrip f_dup(5)
end

@testset "sequential ifs sharing a condition in a loop" begin
    # KA tail-block masking shape: sequential `if cond` diamonds sharing an
    # opaque condition. `opaque`: non-folding cond; `sink`: side effect, no value.
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    @noinline sink(x) = (Base.donotdelete(x); nothing)

    # 2nd if updates an escaping accumulator; the 1st if's phi-free merge must not
    # be absorbed as a pass-through (→ "SSA values used but not defined").
    function seq_ifs_loop(n::Int, c::Bool)
        cond = opaque(c)
        acc = 0
        for kt in 1:n
            if cond; sink(kt); end
            if cond; acc += kt; end
        end
        return acc
    end
    @test @roundtrip seq_ifs_loop(5, true)
    @test @roundtrip seq_ifs_loop(5, false)
    @test @roundtrip seq_ifs_loop(10, true)

    # `y` is defined on one edge only → its merge phi is typed `Core.Const`,
    # illegal in a structural type position unless widened.
    function const_merge_phi(c::Bool)
        cond = opaque(c)
        if cond; x = 3.0; else; x = 4.0; end
        if cond; y = 1.0; end
        return cond ? y : x
    end
    @test @roundtrip const_merge_phi(true)
    @test @roundtrip const_merge_phi(false)
end

@testset "type preservation" begin
    sci, _ = code_structured(Tuple{Float64}) do x::Float64
        x + 1.0
    end |> only

    # Float64 type should be preserved in entry block types
    @test !isempty(sci.entry.body)
    @test any(p -> last(p).type isa Type && last(p).type <: AbstractFloat, sci.entry.body)
    @test @roundtrip (x -> x + 1.0)(3.14)
end

@testset "multiple arguments" begin
    sci, _ = code_structured(Tuple{Int, Float64}) do x::Int, y::Float64
        x + y
    end |> only
    @test sci.entry.terminator isa Core.ReturnNode
    @test @roundtrip ((x::Int, y::Float64) -> x + y)(3, 1.5)
end

@testset "swap_loop phi references" begin
    # Swap pattern stays as LoopOp (break/continue values differ at used positions)
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            x, y = 1, 2
            @check "loop"
            for i in 1:n
                x, y = y, x
            end
            return x
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n::Int
        x, y = 1, 2
        for i in 1:n
            x, y = y, x
        end
        return x
    end |> only

    function f_swap(n::Int)
        x, y = 1, 2
        for i in 1:n; x, y = y, x; end
        x
    end
    @test @roundtrip f_swap(0)
    @test @roundtrip f_swap(1)
    @test @roundtrip f_swap(4)
end

@testset "while loop with outer capture has Nothing type" begin
    # Regression test: a while loop with only outer captures (no actual results)
    # should have Nothing result type, not the type of the outer capture.

    sci, _ = code_structured(Tuple{Int}) do x::Int
        while x > 0
        end
        return x
    end |> only


    # Find the loop in the structure (may be LoopOp, WhileOp, or ForOp)
    matches = filter(p -> p[2].stmt isa LoopOp || p[2].stmt isa WhileOp || p[2].stmt isa ForOp, sci.entry.body)
    @test length(matches) == 1
    (_, entry) = only(matches)
    # Check that the result type is Tuple{} (no results), not Int
    @test entry.type === Tuple{}
end

@testset "while loop ConditionOp uses BlockArgs not SSAValues" begin
    # Regression test: ConditionOp args should be BlockArgs, not SSAValues.

    sci, _ = code_structured(Tuple{Int, Int}) do x::Int, y::Int
        count = 0
        while x^count < y
            count += 1
        end
        return count
    end |> only


    (_, entry) = only(filter(p -> p[2].stmt isa WhileOp, sci.entry.body))
    while_op = entry.stmt
    before = while_op.before

    @test before.terminator isa ConditionOp
    cond_op = before.terminator

    # The result should be BlockArgument, not SSAValue
    @test !isempty(cond_op.args)
    @test cond_op.args[1] isa IRStructurizer.BlockArgument

    f_pow = (x::Int, y::Int) -> (count=0; while x^count<y; count+=1; end; count)
    @test @roundtrip f_pow(2, 16)
    @test @roundtrip f_pow(2, 1)
end

@testset "SESE while-loop and for-in-range both become ForOp" begin
    # Simple SESE while-loop → ForOp
    sci_while, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        acc = 0
        while i < n
            acc += i
            i += 1
        end
        return acc
    end |> only

    for_ops = filter(x -> x isa ForOp, collect(statements(sci_while.entry.body)))
    @test length(for_ops) == 1

    # Native for-in-range (iterator protocol) → also promoted to ForOp
    sci_for, _ = code_structured(Tuple{Int}) do n::Int
        acc = 0
        for i in 1:n
            acc += i
        end
        return acc
    end |> only

    @test sci_for isa StructuredIRCode

    f_while_acc = (n::Int) -> (i=0; acc=0; while i<n; acc+=i; i+=1; end; acc)
    @test @roundtrip f_while_acc(5)
    f_forin_acc = (n::Int) -> (acc=0; for i in 1:n; acc+=i; end; acc)
    @test @roundtrip f_forin_acc(5)
end

@testset "while-loop mimicking iterator protocol stays valid" begin
    # A while-loop that performs operations similar to the iterator protocol
    # (multiple branches, comparisons) should still produce valid structured IR.
    # This previously caused issues when non-SESE loops were incorrectly matched.
    sci, _ = code_structured(Tuple{Int}) do n::Int
        # Mimic iterator: check if done, extract value, update state
        state = 1
        upper = n
        acc = 0
        while true
            # "done" check - similar to iterator protocol
            done = state > upper
            done && break
            # "extract" value
            i = state
            # body
            acc += i
            # "next" state
            state += 1
        end
        return acc
    end |> only

    # Should produce valid structured IR (no unstructured control flow)

    f_iter = (n::Int) -> (state=1; upper=n; acc=0;
        while true; done=state>upper; done&&break; i=state; acc+=i; state+=1; end; acc)
    @test @roundtrip f_iter(5)
    @test @roundtrip f_iter(0)
end

# If-then (no else) must yield phi values, not return Nothing
@testset "if-then yields phi values" begin
    @test @filecheck begin
        code_structured(Tuple{Bool}) do flag::Bool
            x = 0
            @check "if"
            if flag
                x = 1
            end
            @check "yield"
            @check "else"
            @check "yield"
            @check "getfield"
            return x
        end
    end
    f_ifthen = (flag::Bool) -> (x=0; if flag; x=1; end; x)
    @test @roundtrip f_ifthen(true)
    @test @roundtrip f_ifthen(false)
end

@testset "if-then phi inside loop" begin
    # (`<` rather than `<=`: the latter has no proof for a dynamic `n` and would
    # stay a WhileOp.)
    @test @filecheck begin
        code_structured(Tuple{Int, Bool}) do n::Int, flag::Bool
            acc = 0
            j = 1
            @check "= for"
            while j < n
                x = 0
                @check "if"
                if flag && j >= 2
                    x = 1
                end
                @check "yield"
                @check "getfield"
                acc += x
                j += 1
            end
            return acc
        end
    end
end

@testset "if-then with multiple phis" begin
    @test @filecheck begin
        code_structured(Tuple{Bool}) do flag::Bool
            x, y = 0, 0
            @check "if"
            if flag
                x, y = 1, 2
            end
            @check "yield"
            @check "getfield"
            @check "getfield"
            return x + y
        end
    end
    function f_mphi(flag::Bool)
        x, y = 0, 0
        if flag; x, y = 1, 2; end
        x + y
    end
    @test @roundtrip f_mphi(true)
    @test @roundtrip f_mphi(false)
end

@testset "outer IV used inside inner loop" begin
    sci, _ = code_structured(Tuple{Int, Int}) do n::Int, m::Int
        acc = 0
        i = 0
        while i < n
            j = 0
            while j < m
                acc += i  # outer IV used in inner body
                j += 1
            end
            i += 1
        end
        return acc
    end |> only


    # Verify the inner ForOp threads outer IV through as an extra init_value
    outer_for = nothing
    for (_, entry) in sci.entry.body
        if entry.stmt isa ForOp
            outer_for = entry.stmt
            break
        end
    end
    @test outer_for !== nothing

    inner_for = nothing
    for (_, entry) in outer_for.body.body
        if entry.stmt isa ForOp
            inner_for = entry.stmt
            break
        end
    end
    @test inner_for !== nothing

    # Inner ForOp should have extra init_values for threaded outer BlockArgs.
    # Original inner loop has 1 non-IV init_value (acc).
    # The outer loop's subs has 2 entries (IV i + carried acc), both threaded through.
    # After fix: 1 (acc) + 2 (outer IV + outer acc) = 3 init_values
    @test length(inner_for.init_values) == 3
    @test length(inner_for.body.args) == 3

    f_outer_iv = (n::Int, m::Int) -> (acc=0; i=0; while i<n; j=0; while j<m; acc+=i; j+=1; end; i+=1; end; acc)
    @test @roundtrip f_outer_iv(3, 4)
    @test @roundtrip f_outer_iv(0, 4)
end

@testset "ForOp body.args order matches init_values (extra exits)" begin
    # Regression test: pad_extra_exits! must append AFTER header phi BlockArgs,
    # so body.args[i] and init_values[i] have matching types positionally.
    # The inner for-loop threads outer BlockArgs as extra exits; verify the
    # header phi (acc) comes first in init(), before extra exits.
    sci, _ = code_structured(Tuple{Int, Int}) do n::Int, m::Int
        acc = 0
        i = 0
        while i < n
            j = 0
            while j < m
                acc += i
                j += 1
            end
            i += 1
        end
        return acc
    end |> only


    outer_for = nothing
    for (_, entry) in sci.entry.body
        entry.stmt isa ForOp && (outer_for = entry.stmt; break)
    end
    @test outer_for !== nothing
    inner_for = nothing
    for (_, entry) in outer_for.body.body
        entry.stmt isa ForOp && (inner_for = entry.stmt; break)
    end
    @test inner_for !== nothing

    # Header phi (acc) should be body.args[1]; extra exits follow.
    @test length(inner_for.body.args) == length(inner_for.init_values)
    @test length(inner_for.body.args) >= 1
    @test inner_for.body.args[1].id != inner_for.iv_arg.id  # first non-IV arg has different ID from IV
end

@testset "extra exit values don't collide with loop body defs" begin
    # Regression: pad_extra_exits! reused the loop-body SSA index for the outer
    # getfield extraction, producing duplicate SSA defs across scopes.
    # validate_ssa_uniqueness (called by StructuredIRCode constructor) catches this.
    sci, _ = code_structured(Tuple{Int, Int}) do n::Int, m::Int
        acc = 0
        i = 0
        while i < n
            acc += i * m
            i += 1
        end
        return acc
    end |> only
    @test sci isa StructuredIRCode
    f_extra = (n::Int, m::Int) -> (acc=0; i=0; while i<n; acc+=i*m; i+=1; end; acc)
    @test @roundtrip f_extra(5, 3)
end

@testset "for-in-range loop exit condition in non-header block" begin
    # Regression test: Julia's `for i in 1:n` generates IR where the loop header's
    # GotoIfNot (i == upper?) is an inner branch (both targets inside the loop),
    # NOT the loop exit. The actual exit condition (not_at_upper) is in a later
    # merge block. The old code incorrectly used the header's GotoIfNot as the
    # exit condition, which meant:
    #   1. The iterator advance (add_int for i+1) was missing from the loop body
    #   2. The exit condition used === (inner comparison) instead of not_int (actual exit)
    function mysum(n::Int)
        s = 0
        for i in 1:n
            s += i
        end
        s
    end

    # Verify the for-in-range is promoted to ForOp with accumulator in the body.
    # The iterator protocol (===, not_int, advance) is absorbed by ForOp detection.
    @test @filecheck begin
        code_structured(mysum, Tuple{Int})
        @check "for"
        @check "add_int"   # accumulator: s += i
    end

    sci, _ = only(code_structured(mysum, Tuple{Int}))

    @test @roundtrip mysum(5)
    @test @roundtrip mysum(0)
end

@testset "unreachable blocks are ignored" begin
    # IR with unreachable blocks (e.g., from :meta nodes placed in dead blocks)
    # should be handled gracefully by skipping them during structurization.
    f_simple(x::Int) = x + 1
    ir, _ = only(code_ircode(f_simple, (Int,)))

    # Manually add an unreachable block with a :meta node
    nstmts = length(ir.stmts)
    push!(ir.cfg.blocks, Core.Compiler.BasicBlock(
        Core.Compiler.StmtRange(nstmts + 1, nstmts + 1),
        Int[],  # no predecessors — unreachable
        Int[],  # no successors
    ))
    # Add a dummy statement for the unreachable block
    Core.Compiler.resize!(ir.stmts, nstmts + 1)
    inst = ir.stmts[nstmts + 1]
    @static if VERSION >= v"1.12-"
        inst[:stmt] = Expr(:meta, :test, :dummy)
        inst[:type] = Nothing
        inst[:info] = Core.Compiler.NoCallInfo()
        inst[:line] = (Int32(0), Int32(0), Int32(0))
        inst[:flag] = Core.Compiler.IR_FLAGS_EFFECTS
    else
        Core.Compiler.setindex!(inst, Expr(:meta, :test, :dummy), :stmt)
        Core.Compiler.setindex!(inst, Nothing, :type)
        Core.Compiler.setindex!(inst, Core.Compiler.NoCallInfo(), :info)
        Core.Compiler.setindex!(inst, Int32(0), :line)
        Core.Compiler.setindex!(inst, Core.Compiler.IR_FLAGS_EFFECTS, :flag)
    end

    # This should succeed — unreachable block is skipped
    sci = StructuredIRCode(ir)

    @test sci.entry.terminator isa Core.ReturnNode
end

@testset "REGION_PROPER: short-circuit || pattern" begin
    # This was broken: handle_block_region! silently dropped merge phis
    sci, _ = code_structured(Tuple{Int, Int}) do x::Int, y::Int
        r = 0
        if x > 0 || y > 0
            r = 1
        end
        r
    end |> only

    # Verify the output has nested IfOps (from || lowering)
    if_ops = filter(x -> x isa IfOp, collect(statements(sci.entry.body)))
    @test !isempty(if_ops)

    f_or = (x::Int, y::Int) -> (r=0; if x>0||y>0; r=1; end; r)
    @test @roundtrip f_or(1, -1)
    @test @roundtrip f_or(-1, 1)
    @test @roundtrip f_or(-1, -1)
end

@testset "REGION_PROPER: short-circuit && pattern" begin
    sci, _ = code_structured(Tuple{Int, Int}) do x::Int, y::Int
        r = 0
        if x > 0 && y > 0
            r = 1
        end
        r
    end |> only

    if_ops = filter(x -> x isa IfOp, collect(statements(sci.entry.body)))
    @test !isempty(if_ops)

    f_and = (x::Int, y::Int) -> (r=0; if x>0&&y>0; r=1; end; r)
    @test @roundtrip f_and(1, 1)
    @test @roundtrip f_and(1, -1)
    @test @roundtrip f_and(-1, -1)
end

@testset "short-circuit && with sub-diamond in else branch" begin
    # `&&` whose else-path is itself a diamond: the multi-entry continuation (the
    # inner diamond) is structured ONCE behind the materialized predicate.
    f_and_diamond = (x::Int, y::Int, z::Int) -> begin
        a = if x > 0 && y > 0
            x * y
        else
            if z > 0
                z + 1
            else
                -z
            end
        end
        a + 100
    end
    @test code_structured(f_and_diamond, Tuple{Int, Int, Int}) isa Vector
    @test @roundtrip f_and_diamond(1,  1,  1)   # %5 && %9 → x*y
    @test @roundtrip f_and_diamond(-1, 1,  1)   # outer-else → z+1
    @test @roundtrip f_and_diamond(1, -1,  1)   # then → inner-else → z+1
    @test @roundtrip f_and_diamond(-1,-1, -1)   # outer-else → -z
    @test @roundtrip f_and_diamond(1, -1, -1)   # then → inner-else → -z
end

@testset "short-circuit || with sub-diamond in then branch" begin
    # Symmetric `||`: the value-producing then-body (inner diamond) is the
    # multi-entry continuation; gated once, body + skip values threaded as results.
    f_or_diamond = (x::Int, y::Int, z::Int) -> begin
        a = if x > 0 || y > 0
            if z > 0
                z + 1
            else
                -z
            end
        else
            x * y
        end
        a + 100
    end
    @test code_structured(f_or_diamond, Tuple{Int, Int, Int}) isa Vector
    @test @roundtrip f_or_diamond(1,  1,  1)
    @test @roundtrip f_or_diamond(-1, 1,  1)
    @test @roundtrip f_or_diamond(1, -1,  1)
    @test @roundtrip f_or_diamond(-1,-1, -1)
    @test @roundtrip f_or_diamond(1, -1, -1)
end

@testset "short-circuit || guarding a phi-free side-effect body" begin
    # `if a || b { side_effect }` with a phi-free body: previously dropped (the
    # body lands in neither arm region). Now gated once via the multiplexer.
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool

    # Recursively count `:call` statements whose callee is `GlobalRef(_, fname)`
    # across all nested control-flow blocks. Used to assert the side-effecting
    # store appears exactly once (no body duplication).
    function count_calls(blk::Block, fname::Symbol)
        n = 0
        for (_, entry) in blk.body
            stmt = entry.stmt
            if stmt isa Expr && stmt.head === :call
                callee = get(stmt.args, 1, nothing)
                callee isa GlobalRef && callee.name === fname && (n += 1)
            elseif stmt isa ControlFlowOp
                for sub in IRStructurizer.blocks(stmt)
                    n += count_calls(sub, fname)
                end
            end
        end
        return n
    end

    # --- || guarding a Ref store (no value escapes) ---
    function orfun!(r::Base.RefValue{Int}, flag::Bool, g::Int)
        if opaque(flag) || g != 0
            r[] = 99
        end
        return nothing
    end
    sci_or, _ = code_structured(orfun!, Tuple{Base.RefValue{Int}, Bool, Int}) |> only
    # The store appears EXACTLY ONCE — no body duplication.
    @test count_calls(sci_or.entry, :setfield!) == 1
    for (flag, g) in ((false, 0), (false, 5), (true, 0), (true, 5))
        r = Ref(0)
        execute(sci_or, r, flag, g)
        @test r[] == ((flag || g != 0) ? 99 : 0)
    end

    # --- && guarding a Ref store (regression: must still gate correctly) ---
    function andfun!(r::Base.RefValue{Int}, a::Bool, b::Bool)
        if opaque(a) && opaque(b)
            r[] = 99
        end
        return nothing
    end
    sci_and, _ = code_structured(andfun!, Tuple{Base.RefValue{Int}, Bool, Bool}) |> only
    @test count_calls(sci_and.entry, :setfield!) == 1
    for (a, b) in ((false, false), (false, true), (true, false), (true, true))
        r = Ref(0)
        execute(sci_and, r, a, b)
        @test r[] == ((a && b) ? 99 : 0)
    end

    # --- 3-way || (a || b || c) guarding a side effect (generalizes) ---
    function or3!(r::Base.RefValue{Int}, a::Bool, b::Bool, c::Int)
        if opaque(a) || opaque(b) || c != 0
            r[] = 99
        end
        return nothing
    end
    sci_or3, _ = code_structured(or3!, Tuple{Base.RefValue{Int}, Bool, Bool, Int}) |> only
    @test count_calls(sci_or3.entry, :setfield!) == 1
    for (a, b, c) in ((false, false, 0), (false, false, 5),
                      (false, true, 0), (true, false, 0), (true, true, 9))
        r = Ref(0)
        execute(sci_or3, r, a, b, c)
        @test r[] == ((a || b || c != 0) ? 99 : 0)
    end

    # --- mixed (a || b) && c guarding a side effect (must stay correct) ---
    function mixfun!(r::Base.RefValue{Int}, a::Bool, b::Bool, c::Bool)
        if (opaque(a) || opaque(b)) && opaque(c)
            r[] = 99
        end
        return nothing
    end
    sci_mix, _ = code_structured(mixfun!, Tuple{Base.RefValue{Int}, Bool, Bool, Bool}) |> only
    @test count_calls(sci_mix.entry, :setfield!) == 1
    for (a, b, c) in ((false, false, true), (true, false, false),
                      (true, false, true), (false, true, true), (true, true, true))
        r = Ref(0)
        execute(sci_mix, r, a, b, c)
        @test r[] == (((a || b) && c) ? 99 : 0)
    end

    # --- || guarding a side effect INSIDE a loop (KA tail-masking shape) ---
    # The body BB sits in the loop body; blocks dominated by the branch but past
    # the join (the loop latch) must NOT be swallowed into the gated body.
    function or_in_loop!(r::Base.RefValue{Int}, c::Bool, n::Int)
        for k in 1:n
            if opaque(c) || k > 2
                r[] += k
            end
        end
        return nothing
    end
    sci_loop, _ = code_structured(or_in_loop!, Tuple{Base.RefValue{Int}, Bool, Int}) |> only
    @test count_calls(sci_loop.entry, :setfield!) == 1
    for (c, n) in ((false, 5), (true, 5), (false, 2), (true, 0))
        r = Ref(0)
        execute(sci_loop, r, c, n)
        expected = 0
        for k in 1:n
            (c || k > 2) && (expected += k)
        end
        @test r[] == expected
    end

    # --- nested ||-guarded bodies (a gated body inside another) ---
    # The inner `||`'s continuation is the shared outer merge, which lies outside
    # the outer body region — the multiplexer must still gate the inner body once.
    function nested!(r::Base.RefValue{Int}, a::Bool, b::Bool, c::Bool, d::Bool)
        if opaque(a) || opaque(b)
            r[] += 1
            if opaque(c) || opaque(d)
                r[] += 10
            end
        end
        return nothing
    end
    sci_nest, _ = code_structured(nested!, Tuple{Base.RefValue{Int}, Bool, Bool, Bool, Bool}) |> only
    @test count_calls(sci_nest.entry, :setfield!) == 2   # `r[]+=1` and `r[]+=10`, once each
    for a in (false, true), b in (false, true), c in (false, true), d in (false, true)
        r = Ref(0)
        execute(sci_nest, r, a, b, c, d)
        expected = 0
        if a || b
            expected += 1
            (c || d) && (expected += 10)
        end
        @test r[] == expected
    end

    # `||`-guarded body that fans into the continuation at multiple internal points
    # with throw paths (the AcceleratedKernels exclusive-scan shape). Throws give
    # `ipdom(current) == 0`, so an ipdom heuristic fails; the edge-target
    # continuation finds {body, merge} robustly. Body must run iff (inc || iblk!=0).
    function ak_shape!(r::Base.RefValue{Int}, inc::Bool, iblk::Int, k::Int, v::Vector{Int})
        if opaque(inc) || iblk != 0
            # body: a guarded array access (throw path → ipdom 0) and an internal
            # early exit to the continuation, mirroring the `kt == last` early-out.
            x = v[k]            # bounds check → throw/unreachable path
            if k == 1
                r[] = x         # internal exit #1 to the continuation
            else
                r[] = x + 100   # internal exit #2 to the continuation
            end
        end
        return nothing
    end
    tt = Tuple{Base.RefValue{Int}, Bool, Int, Int, Vector{Int}}
    sci_ak, _ = code_structured(ak_shape!, tt) |> only
    # The two body stores stay once each — no tail duplication of the body.
    @test count_calls(sci_ak.entry, :setfield!) == 2
    vv = [11, 22, 33]
    for inc in (false, true), iblk in (0, 2), k in (1, 3)
        r = Ref(-1)
        execute(sci_ak, r, inc, iblk, k, vv)
        expected = -1
        if inc || iblk != 0
            x = vv[k]
            expected = (k == 1) ? x : x + 100
        end
        @test r[] == expected
    end
end

@testset "short-circuit guard with an undef phi slot in the escape check" begin
    # Regression (found via AcceleratedKernels' block merge-sort): a value defined
    # only inside a `||`-guarded body and used inside a SECOND `||`-guard gives the
    # merge phi an undefined incoming slot. find_gated_body's escape check iterated
    # `enumerate(phi.values)`, reading the undef slot before its `isassigned` guard
    # → UndefRefError. It now reads the value only after the guard.
    function undef_phi(c1::Bool, c2::Bool, n::Int)
        if c1 || c2
            t = n + 1
        end
        s = 0
        if c1 || c2
            s = t
        end
        return s
    end
    sci_up, _ = code_structured(undef_phi, Tuple{Bool, Bool, Int}) |> only  # must not throw
    for c1 in (false, true), c2 in (false, true)
        @test execute(sci_up, c1, c2, 7) == undef_phi(c1, c2, 7)
    end
end

@testset "loop exit through fallthrough (not GotoIfNot dest)" begin
    # Regression test: find_loop_exit_condition only checked if GotoIfNot.dest
    # exited the loop, but missed the case where the *fallthrough* path (cond=true)
    # exits. This produced a LoopOp with no break — an infinite loop.
    #
    # The pattern occurs when the iterator protocol merges done/not-done paths
    # into a phi block, and the GotoIfNot there branches to the body (in-loop)
    # on false, while fallthrough exits on true. E.g., SynchArray iteration on 1.11.
    #
    # Synthetic IR:
    #   Block 1: entry → 2
    #   Block 2: header, phi(acc,idx), idx===n?, GotoIfNot → 4
    #   Block 3: done path → 5
    #   Block 4: not-done, next_idx = idx+1 → 5
    #   Block 5: merge phis(next_idx, done_flag, body_idx),
    #            GotoIfNot(done_flag, 7)
    #            dest=7 IN loop, fallthrough=6 OUT → fallthrough exit
    #   Block 6: return acc
    #   Block 7: body, acc += body_idx*body_idx → 2

    CC = Core.Compiler
    nstmts = 17
    stmts = CC.InstructionStream(nstmts)

    @static if VERSION >= v"1.12-"
        _set!(idx, s, t) = (stmts[idx][:stmt]=s; stmts[idx][:type]=t;
            stmts[idx][:info]=CC.NoCallInfo(); stmts[idx][:line]=(Int32(0),Int32(0),Int32(0));
            stmts[idx][:flag]=CC.IR_FLAGS_EFFECTS)
    else
        _set!(idx, s, t) = (CC.setindex!(stmts[idx], s, :stmt); CC.setindex!(stmts[idx], t, :type);
            CC.setindex!(stmts[idx], CC.NoCallInfo(), :info); CC.setindex!(stmts[idx], Int32(0), :line);
            CC.setindex!(stmts[idx], CC.IR_FLAGS_EFFECTS, :flag))
    end

    # Block 1: entry
    _set!(1, GotoNode(2), Nothing)
    # Block 2: loop header
    _set!(2, PhiNode(Int32[1, 7], Any[0, SSAValue(16)]), Int)         # acc
    _set!(3, PhiNode(Int32[1, 7], Any[1, SSAValue(9)]),  Int)         # idx
    _set!(4, Expr(:call, GlobalRef(Base, :(===)), SSAValue(3), Core.Argument(2)), Bool)
    _set!(5, GotoIfNot(SSAValue(4), 4), Nothing)                      # NOT done → 4
    # Block 3: done → merge
    _set!(6, GotoNode(5), Nothing)
    # Block 4: not-done
    _set!(7, Expr(:call, GlobalRef(Base, :add_int), SSAValue(3), 1), Int)
    _set!(8, GotoNode(5), Nothing)
    # Block 5: merge — exit through fallthrough
    _set!(9,  PhiNode(Int32[4, 3], Any[SSAValue(7), 0]),   Int)       # next_idx
    _set!(10, PhiNode(Int32[4, 3], Any[false, true]),       Bool)      # done_flag
    _set!(11, PhiNode(Int32[4, 3], Any[SSAValue(7), 0]),    Int)       # body_idx
    _set!(12, GotoIfNot(SSAValue(10), 7), Nothing)                     # NOT done → 7; done → fall to 6
    # Block 6: exit
    _set!(13, ReturnNode(SSAValue(2)), Nothing)
    # Block 7: body
    _set!(14, Expr(:call, GlobalRef(Base, :mul_int), SSAValue(11), SSAValue(11)), Int)
    _set!(15, Expr(:call, GlobalRef(Base, :add_int), SSAValue(2), SSAValue(14)), Int)
    _set!(16, SSAValue(15), Int)
    _set!(17, GotoNode(2), Nothing)

    cfg = CC.CFG(
        [
            CC.BasicBlock(CC.StmtRange(1, 1),    Int[],    [2]),
            CC.BasicBlock(CC.StmtRange(2, 5),    [1, 7],   [3, 4]),
            CC.BasicBlock(CC.StmtRange(6, 6),    [2],      [5]),
            CC.BasicBlock(CC.StmtRange(7, 8),    [2],      [5]),
            CC.BasicBlock(CC.StmtRange(9, 12),   [3, 4],   [6, 7]),
            CC.BasicBlock(CC.StmtRange(13, 13),  [5],      Int[]),
            CC.BasicBlock(CC.StmtRange(14, 17),  [5],      [2]),
        ],
        Int[1]
    )

    argtypes = Any[Nothing, Int]
    @static if VERSION >= v"1.12-"
        debuginfo = CC.DebugInfoStream(Int32[0 for _ in 1:nstmts])
        ir = CC.IRCode(stmts, cfg, debuginfo, argtypes, Expr[], CC.VarState[])
    else
        ir = CC.IRCode(stmts, cfg, Core.LineInfoNode[], argtypes, Expr[], CC.VarState[])
    end

    sci = StructuredIRCode(ir)


    # Must be a LoopOp (not ForOp — the multi-block header prevents ForOp detection)
    loop_ops = filter(x -> x isa LoopOp, collect(statements(sci.entry.body)))
    @test length(loop_ops) == 1

    # The loop must have a break (via an IfOp with BreakOp in one branch)
    function has_break(block::Block)
        for (_, entry) in block.body
            s = entry.stmt
            s isa IfOp && (has_break(s.then_region) || has_break(s.else_region)) && return true
            s isa LoopOp && has_break(s.body) && return true
        end
        return block.terminator isa BreakOp
    end
    @test has_break(loop_ops[1].body)
end

@testset "proper region merge block with downstream control flow" begin
    # When a proper region's merge block has further control flow (e.g., if/return),
    # the structurizer must process the merge block's subtree — not just its raw
    # statements. Regression: mod(::Float64, ::Float64) lost the final if/return
    # because handle_proper_region! only emitted raw merge-block statements.
    sci, _ = code_structured(mod, Tuple{Float64, Float64}) |> only

    # Count ReturnNodes recursively — every branch must reach one
    function count_returns(blk::Block)
        n = blk.terminator isa Core.ReturnNode ? 1 : 0
        for (_, entry) in blk.body
            if entry.stmt isa IfOp
                n += count_returns(entry.stmt.then_region)
                n += count_returns(entry.stmt.else_region)
            end
        end
        return n
    end
    @test count_returns(sci.entry) >= 3
    # Fixed: vertices_between was over-including dead-end vertices (block 14) into
    # inner REGION_PROPER, causing collect_proper_merge_phis to lose phi edges.
    @test @roundtrip mod(7.5, 2.5)
    @test @roundtrip mod(-3.0, 2.0)
end

end  # regression

#=============================================================================
 Integration Tests: Julia for-in-range patterns
=============================================================================#

@testset "Julia for-in-range integration" begin


@testset "sum_to_n: accumulator pattern" begin
    # Native for-in-range is promoted to ForOp
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            acc = 0
            @check "for"
            for i in 1:n
                @check "add_int"
                acc += i
            end
            return acc
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n
        acc = 0
        for i in 1:n
            acc += i
        end
        return acc
    end |> only

    f_sum = (n) -> (acc=0; for i in 1:n; acc+=i; end; acc)
    @test @roundtrip f_sum(5)
    @test @roundtrip f_sum(0)
end

@testset "product: multiply pattern" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            acc = 1
            @check "for"
            for i in 1:n
                @check "mul_int"
                acc *= i
            end
            return acc
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n
        acc = 1
        for i in 1:n
            acc *= i
        end
        return acc
    end |> only

    f_prod = (n) -> (acc=1; for i in 1:n; acc*=i; end; acc)
    @test @roundtrip f_prod(5)
    @test @roundtrip f_prod(0)
end

@testset "count_evens: conditional accumulator" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            count = 0
            for i in 1:n
                @check "if"
                @check "rem_int"
                if i % 2 == 0
                    count += 1
                end
            end
            return count
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n
        count = 0
        for i in 1:n
            if i % 2 == 0
                count += 1
            end
        end
        return count
    end |> only

    f_evens = (n) -> (count=0; for i in 1:n; if i%2==0; count+=1; end; end; count)
    @test @roundtrip f_evens(6)
    @test @roundtrip f_evens(0)
end

@testset "multiple accumulators" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            sum = 0
            count = 0
            @check "for"
            for i in 1:n
                @check "add_int"
                sum += i
                @check "add_int"
                count += 1
            end
            return sum, count
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n
        sum = 0
        count = 0
        for i in 1:n
            sum += i
            count += 1
        end
        return sum, count
    end |> only

    f_multi_acc = (n) -> (sum=0; count=0; for i in 1:n; sum+=i; count+=1; end; (sum, count))
    @test @roundtrip f_multi_acc(5)
end

@testset "nested for-in-range loops" begin
    # Both native for-in-range loops are promoted to ForOp
    @test @filecheck begin
        code_structured(Tuple{Int, Int}) do n, m
            acc = 0
            @check "for"
            for i in 1:n
                @check "for"
                for j in 1:m
                    @check "mul_int"
                    acc += i * j
                end
            end
            return acc
        end
    end

    sci, _ = code_structured(Tuple{Int, Int}) do n, m
        acc = 0
        for i in 1:n
            for j in 1:m
                acc += i * j
            end
        end
        return acc
    end |> only

    f_nested_forin = (n, m) -> (acc=0; for i in 1:n; for j in 1:m; acc+=i*j; end; end; acc)
    @test @roundtrip f_nested_forin(3, 4)
end

@testset "nested loops with an inner value escaping the outer loop" begin
    # Constant bounds avoid an entry guard/merge between the loops, so the inner
    # result directly escapes both loops and must use the enclosing rename.
    f_const = (x) -> (for i in 1:2; for j in 1:2; x = x * (i + j); end; end; x)
    @test @roundtrip f_const(1.5f0)
    f_noi = (x) -> (for i in 1:2; for j in 1:2; x = x * 0.5f0; end; end; x)
    @test @roundtrip f_noi(1.5f0)
    f_comma = (x) -> (for i in 1:2, j in 1:2; x = x * (i + j); end; x)
    @test @roundtrip f_comma(1.5f0)
    f_triple = (x) -> (for i in 1:2; for j in 1:2; for k in 1:2; x = x * (i + j + k); end; end; end; x)
    @test @roundtrip f_triple(1.5f0)
    # The inner loop's header arg (`x`) is the value escaping the outer loop.
    f_while_in_for = (x) -> (for i in 1:2; j = 1; while j <= 2; x = x * (i + j); j += 1; end; end; x)
    @test @roundtrip f_while_in_for(1.5f0)
    # `outer j` makes the inner IV escape. Its use in the outer loop's exit
    # branch must prevent promotion from replacing it with the upper bound.
    f_hdr = (x) -> (j = 0; for i in 1:2; for outer j in 1:2; x = x * (i + j); end; end; x + j)
    @test @roundtrip f_hdr(1.5f0)
    # Also read the IV in a branch between the loops.
    function f_hdr_if(x, c)
        j = 0
        s = 0
        for i in 1:2
            for outer j in 1:2
                x = x * (i + j)
            end
            if c
                s += j
            end
        end
        return x + s
    end
    @test @roundtrip f_hdr_if(1.5f0, true)
    @test @roundtrip f_hdr_if(1.5f0, false)

    # Both loops still promote to ForOp.
    @test @filecheck begin
        code_structured(Tuple{Float32}) do x
            @check "for"
            for i in 1:2
                @check "for"
                for j in 1:2
                    @check "mul_float"
                    x = x * (i + j)
                end
            end
            return x
        end
    end
end

@testset "for-in-range with tuple destructuring" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            x, y = 1, 2
            @check "loop"
            for i in 1:n
                x, y = y, x
            end
            return x
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n
        x, y = 1, 2
        for i in 1:n
            x, y = y, x
        end
        return x
    end |> only

end

@testset "escaping IV read only inside a nested region after the loop" begin
    # Reads in a later branch must keep the IV carry during promotion.
    f_if = (x, c) -> (j = 0; s = 0; for outer j in 1:2; x = x * j; end; if c; s += j; end; x + s)
    @test @roundtrip f_if(1.5f0, true)
    @test @roundtrip f_if(1.5f0, false)
    f_if_n = (n, c) -> (last = 0; for i in 1:n; last = i; end; c ? last : -1)
    for n in (0, 1, 3), c in (false, true)
        @test @roundtrip f_if_n(n, c)
    end
end

@testset "for-in-range whose loop var escapes is a kept-carry ForOp" begin
    # `for i in 1:n; last = i; end; return last` copies the loop variable into
    # `last`. For a `1:n` range the iterate protocol makes `last` a value#1 shadow of
    # the loop state, and `last` is read after the loop. Promotion keeps `last` as an
    # ordinary carried value whose continue is the induction variable, not the lifted
    # continue (which is the advanced `iv+step`, equal to the bound). The last value
    # is then the last in-body IV (= n), and the empty range is guarded by the outer
    # `if`, so the init (0) is returned for n < 1. Aliasing the shadow to the range's
    # upper bound instead would return `n+1`, a miscompile that earlier had no
    # execution check to catch it (`forlast(1)` gave 2). The exec checks below cover
    # the empty case, so keep them.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            last = 0
            @check "for"
            for i in 1:n
                last = i
            end
            return last
        end
    end

    sci, _ = code_structured(Tuple{Int}) do n
        last = 0
        for i in 1:n
            last = i
        end
        return last
    end |> only
    @test count_stmts(sci.entry, x -> x isa ForOp) == 1

    forlast(n) = (last = 0; for i in 1:n; last = i; end; last)
    for n in (-3, 0, 1, 2, 3, 5, 50, 200)
        @test execute(sci, n) == forlast(n)   # empty → 0; else → n (was n+1 when buggy)
    end

    # Step ≠ 1 (`1:2:n`): the last in-body odd ≤ n. Empty → init 0. The dynamic
    # stepped range stays a general loop (missing proof: `last` on the grid of 1:2),
    # which reads the escaping shadow back the same way.
    forlast2(n) = (last = 0; for i in 1:2:n; last = i; end; last)
    sci2, _ = code_structured(Tuple{Int}) do n
        last = 0
        for i in 1:2:n
            last = i
        end
        return last
    end |> only
    @test count_stmts(sci2.entry, x -> x isa ForOp) == 0
    for n in (-3, 0, 1, 2, 4, 5, 6, 50, 200)
        @test execute(sci2, n) == forlast2(n)
    end

    # Escaping index-capture shadow read *in-body* alongside a real accumulator
    # (the shadow's in-body uses must resolve to the IV, not the write-only carry).
    forboth(n) = (last = 0; acc = 0; for i in 1:n; acc += i; last = i; end; last + acc)
    sci3, _ = code_structured(Tuple{Int}) do n
        last = 0; acc = 0
        for i in 1:n
            acc += i
            last = i
        end
        return last + acc
    end |> only
    @test count_stmts(sci3.entry, x -> x isa ForOp) == 1
    for n in (-3, 0, 1, 2, 5, 50, 200)
        @test execute(sci3, n) == forboth(n)
    end
end

@testset "for-in-range with Int32 bounds" begin
    function simple_for_loop(n::Int32)
        acc = Int32(0)
        for i in Int32(1):n
            acc += i
        end
        return acc
    end

    sci, _ = only(code_structured(simple_for_loop, Tuple{Int32}))


    @test sci isa StructuredIRCode
end

@testset "for-in-range with mixed types (Int32 iterator, Float32 accumulator)" begin
    function mixed_type_loop(data::Vector{Float32}, n::Int32)
        acc = 0.0f0
        for i in Int32(1):n
            acc += data[i]
        end
        return acc
    end

    sci, _ = only(code_structured(mixed_type_loop, Tuple{Vector{Float32}, Int32}))


    @test sci isa StructuredIRCode
end

@testset "constant-bound for-loop with post-loop use" begin
    @test @filecheck begin
        code_structured(Tuple{Int32}) do x::Int32
            acc = Int32(0)
            @check "for"
            for i in Int32(1):Int32(4)
                @check "add_int"
                acc += i
            end
            @check "add_int"
            @check "return"
            return acc + x
        end
    end
end

@testset "runtime-bound for-loop with post-loop use" begin
    @test @filecheck begin
        code_structured(Tuple{Int32, Int32}) do x::Int32, n::Int32
            acc = Int32(0)
            for i in Int32(1):n
                acc += i
            end
            @check "add_int"
            @check "return"
            return acc + x
        end
    end
end

@testset "descending for-in-range stays as LoopOp" begin
    f_desc = (n::Int) -> (s=0; for i in n:-1:0; s+=i; end; s)
    @test @roundtrip f_desc(5)
    @test @roundtrip f_desc(0)
end

@testset "StepRange ForOp has no duplicate undef carries" begin
    # Regression: the iteration protocol produces two carries with the same continue
    # value — the real accumulator (init=0.0f0) and a shadow (init=undef). Before the
    # fix, the ForOp kept both and downstream getfield used the undef-initialized one.
    sci, _ = code_structured(Tuple{Int32, Int32, Int32}) do start::Int32, step::Int32, stop::Int32
        acc = 0.0f0
        for i in start:step:stop
            acc += Float32(i)
        end
        return acc
    end |> only

    for_ops = filter(x -> x isa ForOp, collect(statements(sci.entry.body)))
    if !isempty(for_ops)
        fop = first(for_ops)
        @test length(fop.init_values) == 1
        @test !(fop.init_values[1] isa IRStructurizer.Undef)
    end

    f_step = (s::Int32, st::Int32, sp::Int32) -> (acc=0.0f0; for i in s:st:sp; acc+=Float32(i); end; acc)
    @test @roundtrip f_step(Int32(1), Int32(2), Int32(10))
    @test @roundtrip f_step(Int32(1), Int32(1), Int32(5))
    @test @roundtrip f_step(Int32(5), Int32(1), Int32(0))  # empty range
end

end  # Julia for-in-range integration

@testset "BlockArgument uniqueness across sibling loops" begin
    # Sequential for-in-range loops produce sibling LoopOps (wrapped in IfOps).
    # Each loop's block args must have globally unique IDs so they don't collide
    # when used as dictionary keys (e.g., in DCE dependency graphs).
    sci, _ = code_structured(Tuple{Int32}) do n::Int32
        acc = Int32(0)
        for i in Int32(1):n
            acc += i
        end
        result = Int32(0)
        for j in Int32(1):n
            result += acc
        end
        return result
    end |> only

    # Collect all BlockArguments from all blocks
    all_args = BlockArgument[]
    for blk in eachblock(sci)
        append!(all_args, arguments(blk))
    end

    # All block args must be unique (no two equal values)
    @test length(all_args) == length(unique(all_args))
end

@testset "throw inside a loop is preserved (not dropped as a bare break)" begin
    # A throw INSIDE a counted loop exits the loop to a dead-end (no-successors,
    # Union{}-typed) block. Previously that block was collapsed to a bare BreakOp,
    # silently DROPPING the throw — the function returned normally on bad input.
    # The exit-block statements (the throw) must now be preserved (emitted in place,
    # terminated by `unreachable`/ReturnNode()).
    function loop_throw(a::Vector{Float32}, n::Int)
        acc = 0.0f0
        for k in 1:n
            x = @inbounds a[k]
            if x < 0.0f0
                throw(DomainError(x))
            end
            acc += x
        end
        return acc
    end
    sci, _ = code_structured(loop_throw, Tuple{Vector{Float32}, Int}) |> only
    # Behavioral: good input sums; a negative element THROWS. (The bug returned
    # normally — the loop-exit throw block had been silently dropped to a bare
    # break.) Executing the structured IR exercises that the throw both survived
    # structurization and fires.
    @test execute(sci, Float32[1, 2, 3], 3) == 6.0f0
    @test_throws DomainError execute(sci, Float32[1, -2, 3], 3)
end
