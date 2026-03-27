using Test
using FileCheck

using IRStructurizer
using Core: SSAValue, ReturnNode

# Internal types used in tests for type-checking structured IR output
using IRStructurizer: Block, ControlFlowOp, IfOp, ForOp, WhileOp, LoopOp,
                      YieldOp, ContinueOp, BreakOp, ConditionOp,
                      validate_scf, validate_terminators, validate_ssa_defs,
                      statements, BlockArg
using Base: code_ircode

# Used by "step defined inside loop body" test — must be module-level const
const _STEP_REF = Ref(2)

@testset "IRStructurizer" verbose=true begin

#=============================================================================
 Interface Tests
=============================================================================#

@testset "interface" begin

@testset "low-level API" begin
    g(x) = x > 0 ? x + 1 : x - 1
    ir, _ = only(code_ircode(g, (Int,)))

    # Create flat view (no structurization)
    sci_flat = StructuredIRCode(ir; structurize=false, validate=false)
    @test !any(x -> x isa IfOp, statements(sci_flat.entry.body))

    # Create structured view
    sci = StructuredIRCode(ir)
    @test any(x -> x isa IfOp, statements(sci.entry.body))

    # code_structured is a convenience wrapper
    sci2, _ = code_structured(g, Tuple{Int}) |> only
    @test any(x -> x isa IfOp, statements(sci2.entry.body))
end

@testset "validation: UnstructuredControlFlowError" begin
    # Create unstructured view and verify validation fails
    g(x) = x > 0 ? x + 1 : x - 1
    ir, _ = only(code_ircode(g, (Int,)))

    # Flat view has GotoIfNot
    sci_flat = StructuredIRCode(ir; structurize=false, validate=false)
    gotoifnot_idx = findfirst(s -> s isa Core.GotoIfNot, ir.stmts.stmt)
    @test gotoifnot_idx !== nothing
    # Check that the GotoIfNot is in the body
    @test any(((_, entry),) -> entry.stmt isa Core.GotoIfNot, sci_flat.entry.body)

    # Validation should throw on unstructured IR
    @test_throws UnstructuredControlFlowError validate_scf(sci_flat)

    # Structured view passes validation
    sci = StructuredIRCode(ir)
    @test !any(expr -> expr isa Core.GotoIfNot, statements(sci.entry.body))
    validate_scf(sci)  # Should not throw
end

@testset "validation: invalid terminators" begin
    # Manually construct malformed IR with missing YieldOp
    then_region = Block()
    else_region = Block()
    if_op = IfOp(true, then_region, else_region)
    entry = Block()
    push!(entry, 1, if_op, Tuple{Int})

    # Validation should catch the missing YieldOp
    @test_throws ErrorException validate_terminators(entry)

    # Verify the error message mentions the issue
    try
        validate_terminators(entry)
    catch e
        @test e isa ErrorException
        @test occursin("then region", e.msg)
        @test occursin("else region", e.msg)
    end
end

@testset "validation: scope-aware undefined SSA" begin
    # Manually construct IR where an SSA value defined inside an IfOp branch
    # is referenced in the outer scope — should be caught by scoped validation.
    then_region = Block()
    push!(then_region, 10, Expr(:call, GlobalRef(Base, :add_int), Core.Argument(2), 1), Int64)
    then_region.terminator = YieldOp([SSAValue(10)])
    else_region = Block()
    else_region.terminator = YieldOp([42])
    if_op = IfOp(Core.Argument(2), then_region, else_region)

    entry = Block()
    push!(entry, 1, if_op, Tuple{Int64})
    push!(entry, 2, Expr(:call, Core.getfield, SSAValue(1), 1), Int64)
    # Reference %10 in outer scope — this is INVALID (defined inside then-branch)
    push!(entry, 3, Expr(:call, GlobalRef(Base, :add_int), SSAValue(10), 1), Int64)
    entry.terminator = Core.ReturnNode(SSAValue(2))

    sci = StructuredIRCode(Any[Any, Int64], Any[], entry, 10)
    @test_throws ErrorException validate_ssa_defs(sci)

    # Same structure but referencing %2 (defined in outer scope) — should pass
    entry2 = Block()
    push!(entry2, 1, if_op, Tuple{Int64})
    push!(entry2, 2, Expr(:call, Core.getfield, SSAValue(1), 1), Int64)
    push!(entry2, 3, Expr(:call, GlobalRef(Base, :add_int), SSAValue(2), 1), Int64)
    entry2.terminator = Core.ReturnNode(SSAValue(3))

    sci2 = StructuredIRCode(Any[Any, Int64], Any[], entry2, 10)
    @test validate_ssa_defs(sci2)
end

@testset "ForOp detection during CFG analysis" begin
    # Test that counting loops are detected as ForOp during CFG analysis
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        while i < n
            i += 1
        end
        return i
    end |> only

    # Counting loop should produce ForOp
    loop_ops = filter(x -> x isa ControlFlowOp, collect(statements(sci.entry.body)))
    @test !isempty(loop_ops)
    @test loop_ops[1] isa ForOp
end

@testset "code_structured single-argument form" begin
    # Single-method function: argtypes inferred from signature
    h_single(x::Int) = x > 0 ? x + 1 : x - 1
    sci1, ret1 = code_structured(h_single) |> only
    @test any(x -> x isa IfOp, statements(sci1.entry.body))
    @test ret1 === Int64

    # Equivalent to explicit argtypes
    sci2, ret2 = code_structured(h_single, Tuple{Int}) |> only
    @test ret1 === ret2

    # Multi-method function: falls back to Tuple, returns all methods
    h_multi(x::Int) = x + 1
    h_multi(x::Float64) = x - 1.0
    results = code_structured(h_multi)
    @test length(results) == 2
end

@testset "display output format" begin
    # Verify display shows proper structure
    sci, _ = code_structured(Tuple{Bool}) do x::Bool
        x ? 1 : 2
    end |> only

    io = IOBuffer()
    show(io, MIME"text/plain"(), sci)
    output = String(take!(io))

    @test occursin("StructuredIRCode", output)
    @test occursin("if ", output)
    @test occursin("else", output)
    @test occursin("return", output)
end

end  # interface

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
end

end  # acyclic regions

@testset "cyclic regions" begin

@testset "simple loop structure - ForOp" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            i = 0
            @check "for %{{.*}} ="
            while i < n
                i += 1
            end
            @check "continue"
            return i
        end
    end
end

@testset "loop with condition" begin
    # Loop with condition check at header (empty body - self-loop pattern)
    @test @filecheck begin
        code_structured(Tuple{Int}) do flag::Int
            @check "loop ->"
            while flag != 0
                @check "not_int"
                # spin
            end
            return flag
        end
    end
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
end

end  # cyclic regions

end  # CFG analysis

#=============================================================================
 Loop Classification Tests
 Tests that loops are correctly classified into ForOp, WhileOp, or LoopOp.
 ForOp is detected directly during CFG analysis for counting patterns.
=============================================================================#

@testset "loop classification" begin

@testset "ForOp detection" begin

@testset "bounded counter" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            i = 0
            @check "for %{{.*}} ="
            while i < n
                i += 1
            end
            @check "continue"
            return i
        end
    end

    # Also verify ForOp bounds programmatically (FileCheck can't check these)
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        while i < n
            i += 1
        end
        return i
    end |> only
    for_ops = filter(x -> x isa ForOp, collect(statements(sci.entry.body)))
    @test length(for_ops) == 1

    for_op = for_ops[1]
    @test for_op.lower == 0
    @test for_op.upper isa Core.Argument
    @test for_op.step == 1
end

@testset "inclusive bound (<=) gets exclusive adjustment" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            i = 0
            acc = 0
            @check "add_int(_2, 1)::Int64"
            @check "for %arg1 = 0:1:%{{.*}}"
            while i <= n
                acc += i
                i += 1
            end
            return acc
        end
    end
end

@testset "inclusive bound with Core.Const upper type" begin
    # Regression test: when the upper bound SSA value has Core.Const inferred type,
    # the inclusive→exclusive adjustment must still work (one() needs a concrete type).
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
end

@testset "Julia for-in-range (1:n) stays as LoopOp" begin
    # Native for-in-range has complex iterator protocol IR (multiple GotoIfNots)
    # so it stays as LoopOp, not ForOp. Use while-loops for ForOp.
    @test @filecheck begin
        code_structured(Tuple{Int}) do n::Int
            acc = 0
            @check "loop"
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
    validate_scf(sci)

    # Verify IR is valid (LoopOp is nested inside IfOps from iterator protocol)
    @test sci isa StructuredIRCode
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

end  # ForOp detection

@testset "WhileOp detection" begin

@testset "condition-only spinloop" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do flag::Int
            @check "loop ->"
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
end

@testset "type preservation" begin
    sci, _ = code_structured(Tuple{Float64}) do x::Float64
        x + 1.0
    end |> only

    # Float64 type should be preserved in entry block types
    @test !isempty(sci.entry.body)
    @test any(((_, entry),) -> entry.typ isa Type && entry.typ <: AbstractFloat, sci.entry.body)
end

@testset "multiple arguments" begin
    sci, _ = code_structured(Tuple{Int, Float64}) do x::Int, y::Float64
        x + y
    end |> only
    @test sci.entry.terminator isa Core.ReturnNode
end

@testset "swap_loop phi references" begin
    # Native for-in-range produces LoopOp (iterator protocol is non-SESE)
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
    validate_scf(sci)
end

@testset "while loop with outer capture has Nothing type" begin
    # Regression test: a while loop with only outer captures (no actual results)
    # should have Nothing result type, not the type of the outer capture.

    sci, _ = code_structured(Tuple{Int}) do x::Int
        while x > 0
        end
        return x
    end |> only
    validate_scf(sci)

    # Find the loop in the structure (may be LoopOp, WhileOp, or ForOp)
    matches = filter(p -> p[2].stmt isa LoopOp || p[2].stmt isa WhileOp || p[2].stmt isa ForOp, sci.entry.body)
    @test length(matches) == 1
    (_, entry) = only(matches)
    # Check that the result type is Tuple{} (no results), not Int
    @test entry.typ === Tuple{}
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
    validate_scf(sci)

    (_, entry) = only(filter(p -> p[2].stmt isa WhileOp, sci.entry.body))
    while_op = entry.stmt
    before = while_op.before

    @test before.terminator isa ConditionOp
    cond_op = before.terminator

    # The result should be BlockArg, not SSAValue
    @test !isempty(cond_op.args)
    @test cond_op.args[1] isa IRStructurizer.BlockArg
end

@testset "SESE while-loop becomes ForOp, non-SESE stays LoopOp" begin
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
    validate_scf(sci_while)
    for_ops = filter(x -> x isa ForOp, collect(statements(sci_while.entry.body)))
    @test length(for_ops) == 1

    # Native for-in-range (non-SESE due to iterator protocol) → LoopOp
    # LoopOp is nested inside IfOps from iterator protocol's branch structure
    sci_for, _ = code_structured(Tuple{Int}) do n::Int
        acc = 0
        for i in 1:n
            acc += i
        end
        return acc
    end |> only
    validate_scf(sci_for)
    # LoopOp will be nested inside IfOps, just verify the IR is valid
    @test sci_for isa StructuredIRCode
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
    validate_scf(sci)
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
end

@testset "if-then phi inside loop" begin
    @test @filecheck begin
        code_structured(Tuple{Int, Bool}) do n::Int, flag::Bool
            acc = 0
            j = 1
            @check "for"
            while j <= n
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
    validate_scf(sci)

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
    validate_scf(sci)

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
    @test inner_for.body.args[1].id == 2  # id 1 = IV, id 2 = first non-IV arg
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

    # Verify the loop body has the correct structure:
    # - add_int for accumulator (s += i)
    # - === for inner comparison (i == upper)
    # - add_int for iterator advance (i + 1) — was MISSING without the fix
    # - not_int for the actual exit condition — was MISPLACED without the fix
    # - if/continue/break using the correct exit condition
    @test @filecheck begin
        code_structured(mysum, Tuple{Int})
        @check "loop"
        @check "add_int"   # accumulator: s += i
        @check "==="       # inner comparison: i == upper
        @check "add_int"   # iterator advance: i + 1
        @check "not_int"   # exit condition computation
        @check "if"        # exit IfOp uses not_int result
        @check "continue"
        @check "break"
    end

    sci, _ = only(code_structured(mysum, Tuple{Int}))
    validate_scf(sci)
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
    validate_scf(sci)
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
    validate_scf(sci)
    validate_ssa_defs(sci)

    # Verify the output has nested IfOps (from || lowering)
    if_ops = filter(x -> x isa IfOp, collect(statements(sci.entry.body)))
    @test !isempty(if_ops)
end

@testset "REGION_PROPER: short-circuit && pattern" begin
    sci, _ = code_structured(Tuple{Int, Int}) do x::Int, y::Int
        r = 0
        if x > 0 && y > 0
            r = 1
        end
        r
    end |> only
    validate_scf(sci)
    validate_ssa_defs(sci)

    if_ops = filter(x -> x isa IfOp, collect(statements(sci.entry.body)))
    @test !isempty(if_ops)
end

end  # regression

#=============================================================================
 Integration Tests: Julia for-in-range patterns
=============================================================================#

@testset "Julia for-in-range integration" begin


@testset "sum_to_n: accumulator pattern" begin
    # Native for-in-range stays as LoopOp (iterator protocol is non-SESE)
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            acc = 0
            @check "loop"
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
    validate_scf(sci)
end

@testset "product: multiply pattern" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            acc = 1
            @check "loop"
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
    validate_scf(sci)
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
    validate_scf(sci)
end

@testset "multiple accumulators" begin
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            sum = 0
            count = 0
            @check "loop"
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
    validate_scf(sci)
end

@testset "nested for-in-range loops" begin
    # Both native for-in-range loops produce LoopOp (iterator protocol is non-SESE)
    @test @filecheck begin
        code_structured(Tuple{Int, Int}) do n, m
            acc = 0
            @check "loop"
            for i in 1:n
                @check "loop"
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
    validate_scf(sci)
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
    validate_scf(sci)
end

@testset "for-in-range produces valid LoopOp" begin
    # Native for-in-range stays as LoopOp (iterator protocol is non-SESE)
    @test @filecheck begin
        code_structured(Tuple{Int}) do n
            last = 0
            @check "loop"
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
    validate_scf(sci)
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
    validate_scf(sci)
    validate_ssa_defs(sci)
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
    validate_scf(sci)
    validate_ssa_defs(sci)
    @test sci isa StructuredIRCode
end

@testset "constant-bound for-loop with post-loop use" begin
    @test @filecheck begin
        code_structured(Tuple{Int32}) do x::Int32
            acc = Int32(0)
            @check "loop init"
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

end  # Julia for-in-range integration

#=============================================================================
 Utilities Tests
=============================================================================#

@testset "utilities" begin

@testset "instructions(block)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    insts = collect(instructions(sci.entry))
    @test !isempty(insts)
    @test all(i -> i isa Inst, insts)

    # Each Inst bundles ssa_idx, stmt, typ
    inst = first(insts)
    @test value_type(inst) isa Type
    @test SSAValue(inst) isa SSAValue
end

@testset "arguments(block)" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        acc = 0
        while i < n
            acc += i
            i += 1
        end
        return acc
    end |> only

    # Entry block has no arguments
    @test isempty(arguments(sci.entry))

    # ForOp body has arguments (IV + carries)
    for inst in instructions(sci.entry)
        if stmt(inst) isa ForOp
            body_args = arguments(stmt(inst).body)
            @test !isempty(body_args)
            @test all(a -> a isa BlockArg, body_args)
            break
        end
    end
end

@testset "blocks(op)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x > 0 ? x + 1 : x - 1
    end |> only

    for inst in instructions(sci.entry)
        if stmt(inst) isa IfOp
            bs = blocks(stmt(inst))
            @test length(bs) == 2
            @test all(b -> b isa Block, bs)
            break
        end
    end

    # blocks(sci) returns the entry block
    @test blocks(sci) == (sci.entry,)
end

@testset "terminators(block)" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        while i < n
            i += 1
        end
        return i
    end |> only

    for inst in instructions(sci.entry)
        op = stmt(inst)
        if op isa ForOp
            terms = terminators(op.body)
            @test !isempty(terms)
            @test any(t -> t isa ContinueOp, terms)
            break
        end
    end
end

@testset "parent chain and root" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x > 0 ? x + 1 : x - 1
    end |> only

    # Entry block parent is the SCI
    @test parent(sci.entry) === sci

    # Nested block parent is the entry block
    for inst in instructions(sci.entry)
        if stmt(inst) isa IfOp
            then_blk = stmt(inst).then_region
            @test parent(then_blk) === sci.entry
            @test IRStructurizer.root(then_blk) === sci
            break
        end
    end
end

@testset "push! / insert_before! / insert_after!" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    old_max = sci.max_ssa_idx

    # push! returns Inst with auto-allocated SSA
    new_inst = push!(sci.entry, Expr(:call, :dummy), Int)
    @test new_inst isa Inst
    @test new_inst.ssa_idx == old_max + 1
    @test sci.max_ssa_idx == old_max + 1

    # insert_before! / insert_after!
    insts = collect(instructions(sci.entry))
    ref = first(insts)
    before = insert_before!(sci.entry, ref, Expr(:call, :before), Int32)
    after = insert_after!(sci.entry, ref, Expr(:call, :after), Int64)
    @test before isa Inst && after isa Inst

    all_insts = collect(instructions(sci.entry))
    bp = findfirst(i -> i == before, all_insts)
    rp = findfirst(i -> i == ref, all_insts)
    ap = findfirst(i -> i == after, all_insts)
    @test bp < rp < ap
end

@testset "delete!(block, inst)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    n_before = length(collect(instructions(sci.entry)))
    dummy = push!(sci.entry, Expr(:call, :dummy), Int)
    @test length(collect(instructions(sci.entry))) == n_before + 1

    delete!(sci.entry, dummy)
    @test length(collect(instructions(sci.entry))) == n_before
end

@testset "uses(block) and UseIndex" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        y = x + 1
        z = y * 2
        return z
    end |> only

    idx = uses(sci.entry)

    # Every instruction result should have the right use count
    for inst in instructions(sci.entry)
        refs = idx[inst]
        @test refs isa Vector
    end

    # Int key normalization works
    for inst in instructions(sci.entry)
        @test idx[inst.ssa_idx] == idx[SSAValue(inst.ssa_idx)]
    end
end

@testset "uses(block, val)" begin
    sci, _ = code_structured(Tuple{Int, Int}) do x::Int, y::Int
        x + y
    end |> only

    # In do-block syntax, Argument(1) is the closure, Argument(2) is x, Argument(3) is y
    # At least one argument should be used in the addition
    refs_x = uses(sci.entry, Core.Argument(2))
    refs_y = uses(sci.entry, Core.Argument(3))
    @test !isempty(refs_x) || !isempty(refs_y)
end

@testset "replace_uses!" begin
    block = Block()
    push!(block.body, (1, Expr(:call, GlobalRef(Base, :+), SSAValue(0), SSAValue(0)), Int))
    push!(block.body, (2, Expr(:call, GlobalRef(Base, :*), SSAValue(1), SSAValue(0)), Int))

    replace_uses!(block, SSAValue(0), SSAValue(99))
    idx = uses(block)
    @test isempty(idx[SSAValue(0)])
    @test length(idx[SSAValue(99)]) == 3
end

@testset "carries(op)" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        acc = 0
        while i < n
            acc += i
            i += 1
        end
        return acc
    end |> only

    found = false
    for inst in instructions(sci.entry)
        op = stmt(inst)
        op isa ForOp || continue
        c = carries(op)
        @test length(c) == length(op.init_values)
        @test length(c) >= 1
        # Access through carries
        cr = c[1]
        @test init_value(cr) !== nothing
        @test body_arg(cr) isa BlockArg
        found = true
        break
    end
    @test found
end

@testset "carries filter!" begin
    # Build a ForOp with 2 carries, filter to keep only the first
    body = Block()
    iv = BlockArg(1, Int)
    a1 = BlockArg(2, Float64)
    a2 = BlockArg(3, Float64)
    # ForOp: IV is in iv_arg, body.args are just the carries
    push!(body.args, a1)
    push!(body.args, a2)
    body.terminator = ContinueOp([SSAValue(10), SSAValue(11)])
    op = ForOp(1, 10, 1, iv, body, [SSAValue(100), SSAValue(101)])

    c = carries(op)
    @test length(c) == 2

    idx_map = filter!(cr -> init_value(cr) == SSAValue(100), c)
    @test length(op.init_values) == 1
    @test length(body.args) == 1  # 1 carry remaining
    @test length(body.terminator.values) == 1
    @test idx_map == Dict(1 => 1)
end

@testset "carries push!" begin
    entry = Block()
    iv = BlockArg(1, Int)
    body = Block()
    body.terminator = ContinueOp(IRStructurizer.IRValue[])
    op = ForOp(1, 10, 1, iv, body, IRStructurizer.IRValue[])
    push!(entry.body, (1, op, Nothing))
    sci = StructuredIRCode(Any[], Any[], entry, 1)
    entry.parent = sci
    body.parent = entry

    c = carries(op)
    @test length(c) == 0

    cr = push!(c, SSAValue(42), Float64)
    @test length(op.init_values) == 1
    @test length(body.args) == 1  # just the new carry (IV is separate)
    @test length(body.terminator.values) == 1
    @test init_value(cr) == SSAValue(42)
    @test body_arg(cr).type == Float64
end

@testset "uses finds all operand positions" begin
    # uses() should find operands in Expr args and in ReturnNode terminators
    block = Block()
    push!(block.body, (1, Expr(:call, GlobalRef(Base, :+), SSAValue(0), SSAValue(0)), Int))
    block.terminator = ReturnNode(SSAValue(1))

    idx = uses(block)
    @test length(idx[SSAValue(0)]) == 2  # two Expr args
    @test length(idx[SSAValue(1)]) == 1  # ReturnNode terminator
end

@testset "replace_uses! mutates all positions" begin
    # Verify replace_uses! works on Expr args
    block = Block()
    push!(block.body, (1, Expr(:call, GlobalRef(Base, :+), SSAValue(0), SSAValue(0)), Int))
    block.terminator = ReturnNode(SSAValue(0))

    replace_uses!(block, SSAValue(0), SSAValue(99))

    # All 3 uses should now be SSAValue(99)
    idx = uses(block)
    @test isempty(idx[SSAValue(0)])
    @test length(idx[SSAValue(99)]) == 3

    # Verify the ReturnNode terminator was actually replaced
    @test block.terminator == ReturnNode(SSAValue(99))
end

@testset "replace_uses! on IfOp condition" begin
    # Build block with IfOp whose condition references SSAValue(5)
    then_blk = Block()
    then_blk.terminator = YieldOp()
    else_blk = Block()
    else_blk.terminator = YieldOp()
    block = Block()
    ifop = IfOp(SSAValue(5), then_blk, else_blk)
    push!(block.body, (1, ifop, Nothing))

    replace_uses!(block, SSAValue(5), SSAValue(42))
    @test ifop.condition == SSAValue(42)
end

@testset "deleteat!(carries, indices)" begin
    body = Block()
    iv = BlockArg(1, Int)
    a1 = BlockArg(2, Float64)
    a2 = BlockArg(3, Float64)
    a3 = BlockArg(4, Float64)
    push!(body.args, a1)
    push!(body.args, a2)
    push!(body.args, a3)
    body.terminator = ContinueOp([SSAValue(10), SSAValue(11), SSAValue(12)])
    op = ForOp(1, 10, 1, iv, body, Any[SSAValue(100), SSAValue(101), SSAValue(102)])

    c = carries(op)
    @test length(c) == 3

    idx_map = deleteat!(c, [2])
    @test length(op.init_values) == 2
    @test length(body.args) == 2
    @test length(body.terminator.values) == 2
    @test idx_map == Dict(1 => 1, 3 => 2)
end

@testset "carries for WhileOp" begin
    before = Block()
    after = Block()
    a1_before = BlockArg(1, Int)
    a2_before = BlockArg(2, Float64)
    push!(before.args, a1_before)
    push!(before.args, a2_before)
    before.terminator = ConditionOp(SSAValue(1), Any[a1_before, a2_before])

    a1_after = BlockArg(1, Int)
    a2_after = BlockArg(2, Float64)
    push!(after.args, a1_after)
    push!(after.args, a2_after)
    after.terminator = YieldOp(Any[SSAValue(20), SSAValue(21)])

    op = WhileOp(before, after, Any[SSAValue(100), SSAValue(101)])

    c = carries(op)
    @test length(c) == 2
    @test body_arg(c[1]) === a1_before
    @test init_value(c[1]) == SSAValue(100)

    # term_value works for ConditionOp and YieldOp
    @test term_value(c[1], before.terminator) === a1_before
    @test term_value(c[1], after.terminator) == SSAValue(20)

    # filter! removes from all sites
    filter!(cr -> init_value(cr) == SSAValue(100), c)
    @test length(op.init_values) == 1
    @test length(before.args) == 1
    @test length(after.args) == 1
    @test length(before.terminator.args) == 1
    @test length(after.terminator.values) == 1
end

@testset "carries for LoopOp" begin
    # Build LoopOp body with IfOp containing ContinueOp and BreakOp
    then_blk = Block()
    then_blk.terminator = BreakOp(Any[SSAValue(50)])
    else_blk = Block()
    else_blk.terminator = ContinueOp(Any[SSAValue(60)])

    body = Block()
    a1 = BlockArg(1, Int)
    push!(body.args, a1)
    ifop = IfOp(SSAValue(1), then_blk, else_blk)
    push!(body.body, (10, ifop, Nothing))
    body.terminator = nothing

    op = LoopOp(body, Any[SSAValue(100)])

    # Wrap in SCI so root() works for push!(carries, ...)
    entry = Block()
    push!(entry.body, (11, op, Nothing))
    sci = StructuredIRCode(Any[], Any[], entry, 11)
    entry.parent = sci
    body.parent = entry
    then_blk.parent = body
    else_blk.parent = body

    c = carries(op)
    @test length(c) == 1

    # push! threads through both ContinueOp and BreakOp
    cr = push!(c, SSAValue(200), Float64)
    @test length(op.init_values) == 2
    @test length(body.args) == 2
    @test length(then_blk.terminator.values) == 2
    @test length(else_blk.terminator.values) == 2
end

@testset "init_value! and term_value! setters" begin
    body = Block()
    iv = BlockArg(1, Int)
    a1 = BlockArg(2, Float64)
    push!(body.args, a1)
    body.terminator = ContinueOp(Any[SSAValue(10)])
    op = ForOp(1, 10, 1, iv, body, Any[SSAValue(100)])

    c = carries(op)
    cr = c[1]

    # init_value!
    init_value!(cr, SSAValue(999))
    @test op.init_values[1] == SSAValue(999)

    # term_value!
    term_value!(cr, body.terminator, SSAValue(888))
    @test body.terminator.values[1] == SSAValue(888)

    # term_value! on ConditionOp
    cond = ConditionOp(SSAValue(1), Any[SSAValue(5)])
    term_value!(cr, cond, SSAValue(777))
    @test cond.args[1] == SSAValue(777)
end

@testset "empty block edge cases" begin
    block = Block()

    @test isempty(collect(instructions(block)))
    @test isempty(uses(block).index)
    @test isempty(terminators(block))
    @test isempty(block)
end

@testset "nested uses" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        acc = 0
        for i in 1:n
            if i > 5
                acc += i
            end
        end
        return acc
    end |> only

    # uses() on the entry block should find use sites at all nesting levels
    idx = uses(sci.entry)
    # At minimum, Argument(2) (n) should be used somewhere
    @test !isempty(idx[Core.Argument(2)])
end

@testset "terminator(block)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    @test terminator(sci.entry) === sci.entry.terminator
    @test terminator(sci.entry) isa ReturnNode
end

@testset "isempty(block)" begin
    @test isempty(Block())

    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only
    @test !isempty(sci.entry)
end

@testset "eachblock(sci)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        if x > 0
            for i in 1:x
                x += i
            end
        end
        return x
    end |> only

    all_blocks = eachblock(sci)
    @test all_blocks[1] === sci.entry
    # Should find more than just the entry block (IfOp + ForOp have sub-blocks)
    @test length(all_blocks) > 1
    @test all(b -> b isa Block, all_blocks)
end

@testset "findblock(sci, inst)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        y = x + 1
        return y
    end |> only

    # Find an instruction in the entry block
    inst = first(instructions(sci.entry))
    found = findblock(sci, inst)
    @test found === sci.entry

    # Non-existent instruction returns nothing
    @test findblock(sci, Inst(999999, nothing, Nothing)) === nothing
end

@testset "pushfirst!(block, stmt, typ)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    old_first = first(instructions(sci.entry))
    new_inst = pushfirst!(sci.entry, Expr(:call, :sentinel), Int)
    @test new_inst isa Inst
    @test first(instructions(sci.entry)) == new_inst
    @test collect(instructions(sci.entry))[2] == old_first
end

@testset "update_type!(block, inst, new_type)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    inst = first(instructions(sci.entry))
    old_type = value_type(inst)
    update_type!(sci.entry, inst, Float64)

    # Re-read from block to verify
    updated = first(instructions(sci.entry))
    @test value_type(updated) == Float64
end

@testset "new_block_arg!(block, typ)" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        while i < n
            i += 1
        end
        return i
    end |> only

    # Find a loop body block with args
    for inst in instructions(sci.entry)
        op = stmt(inst)
        op isa ForOp || continue

        old_n = length(arguments(op.body))
        new_arg = new_block_arg!(op.body, Float32)
        @test new_arg isa BlockArg
        @test new_arg.type == Float32
        @test length(arguments(op.body)) == old_n + 1
        @test arguments(op.body)[end] === new_arg
        break
    end
end

@testset "walk_uses! extensibility" begin
    using IRStructurizer: walk_uses!, IndexedUseRef

    # Custom statement type
    mutable struct TestCustomNode
        operands::Vector{Any}
    end

    # Define walk_uses! for our custom type
    IRStructurizer.walk_uses!(f, node::TestCustomNode) =
        for i in 1:length(node.operands); f(IndexedUseRef(node.operands, i)); end

    block = Block()
    push!(block.body, (1, TestCustomNode([SSAValue(0), SSAValue(0)]), Int))
    push!(block.body, (2, Expr(:call, GlobalRef(Base, :+), SSAValue(1)), Int))
    block.terminator = ReturnNode(SSAValue(2))

    # uses() should find operands inside our custom node
    idx = uses(block)
    @test length(idx[SSAValue(0)]) == 2  # two operands in TestCustomNode

    # replace_uses! should work through custom nodes
    replace_uses!(block, SSAValue(0), SSAValue(99))
    idx2 = uses(block)
    @test isempty(idx2[SSAValue(0)])
    @test length(idx2[SSAValue(99)]) == 2
end

@testset "insert_before!/after! with SSAValue ref" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    insts = collect(instructions(sci.entry))
    ref = first(insts)
    ref_ssaval = SSAValue(ref)

    # insert_before! with SSAValue reference
    before = insert_before!(sci.entry, ref_ssaval, Expr(:call, :before_ssa), Int32)
    @test before isa Inst

    # insert_after! with SSAValue reference
    after = insert_after!(sci.entry, ref_ssaval, Expr(:call, :after_ssa), Int64)
    @test after isa Inst

    # Verify ordering: before < ref < after
    all_insts = collect(instructions(sci.entry))
    bp = findfirst(i -> i == before, all_insts)
    rp = findfirst(i -> i == ref, all_insts)
    ap = findfirst(i -> i == after, all_insts)
    @test bp < rp < ap

    # Chaining: insert_after! the just-inserted instruction
    chained = insert_after!(sci.entry, SSAValue(after), Expr(:call, :chained), Bool)
    all_insts2 = collect(instructions(sci.entry))
    cp = findfirst(i -> i == chained, all_insts2)
    ap2 = findfirst(i -> i == after, all_insts2)
    @test cp == ap2 + 1
end

@testset "resolve_call" begin
    using IRStructurizer: resolve_call

    # :call expression with GlobalRef
    expr_call = Expr(:call, GlobalRef(Base, :+), SSAValue(1), SSAValue(2))
    result = resolve_call(expr_call)
    @test result !== nothing
    func, operands = result
    @test func === Base.:+
    @test length(operands) == 2
    @test operands[1] == SSAValue(1)

    # :invoke expression
    mi = first(methods(+, (Int, Int)))
    expr_invoke = Expr(:invoke, mi, GlobalRef(Base, :+), SSAValue(1), SSAValue(2))
    result2 = resolve_call(expr_invoke)
    @test result2 !== nothing
    func2, operands2 = result2
    @test func2 === Base.:+
    @test length(operands2) == 2

    # Non-call returns nothing
    @test resolve_call(42) === nothing
    @test resolve_call(Expr(:new, :Foo)) === nothing

    # Inst overload
    inst = Inst(1, expr_call, Int)
    result3 = resolve_call(inst)
    @test result3 !== nothing
    @test first(result3) === Base.:+
end

@testset "iscall / callee / callargs" begin
    using IRStructurizer: iscall, callee, callargs

    expr_call = Expr(:call, GlobalRef(Base, :+), SSAValue(1), SSAValue(2))
    @test iscall(expr_call)
    @test callee(expr_call) == GlobalRef(Base, :+)
    @test length(callargs(expr_call)) == 2
    @test callargs(expr_call)[1] == SSAValue(1)

    mi = first(methods(+, (Int, Int)))
    expr_invoke = Expr(:invoke, mi, GlobalRef(Base, :*), SSAValue(3))
    @test iscall(expr_invoke)
    @test callee(expr_invoke) == GlobalRef(Base, :*)
    @test length(callargs(expr_invoke)) == 1

    @test !iscall(42)
    @test !iscall(Expr(:new, :Foo))

    # Inst overloads
    inst = Inst(1, expr_call, Int)
    @test iscall(inst)
    @test callee(inst) == GlobalRef(Base, :+)
    @test length(callargs(inst)) == 2
end

@testset "carries: per-terminator replacement (mwe.jl pattern)" begin
    # This test verifies the pattern from cuTile's mwe.jl:
    # push!(carries, ...) threads a placeholder, then term_value! replaces
    # per-terminator with different values based on control flow path.
    using IRStructurizer: term_value!, carries, body_arg, init_value

    # Build: LoopOp with IfOp inside body (BreakOp in then, ContinueOp in else)
    then_blk = Block()
    then_blk.terminator = BreakOp([SSAValue(99)])     # 1 user carry
    else_blk = Block()
    else_blk.terminator = ContinueOp([SSAValue(88)])   # 1 user carry

    body = Block()
    push!(body.args, BlockArg(1, Int))  # 1 user block arg
    ifop = IfOp(SSAValue(50), then_blk, else_blk)
    push!(body.body, (10, ifop, Nothing))
    body.terminator = nothing

    op = LoopOp(body, Any[SSAValue(100)])  # 1 user init value

    # Wire parents
    entry = Block()
    push!(entry.body, (11, op, Nothing))
    sci = StructuredIRCode(Any[], Any[], entry, 100)
    entry.parent = sci
    body.parent = entry
    then_blk.parent = body
    else_blk.parent = body

    # Push a token carry — placeholder threads through both terminators
    c = carries(op)
    cr = push!(c, SSAValue(200), Float64)
    placeholder = body_arg(cr)

    @test then_blk.terminator.values[2] === placeholder
    @test else_blk.terminator.values[2] === placeholder

    # Now simulate what the token ordering pass does:
    # Replace per-terminator with DIFFERENT values
    new_token = SSAValue(999)   # post-memory-op token for break path
    tok_arg = placeholder       # unchanged body arg for continue path

    term_value!(cr, then_blk.terminator, new_token)
    term_value!(cr, else_blk.terminator, tok_arg)

    # Verify: different values per terminator
    @test then_blk.terminator.values[2] === new_token
    @test else_blk.terminator.values[2] === tok_arg
    @test then_blk.terminator.values[2] !== else_blk.terminator.values[2]

    # Init value and user carries are unchanged
    @test init_value(cr) == SSAValue(200)
    @test then_blk.terminator.values[1] == SSAValue(99)
    @test else_blk.terminator.values[1] == SSAValue(88)
end

end  # utilities

end  # @testset "IRStructurizer"
