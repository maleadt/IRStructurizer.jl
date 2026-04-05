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
    f_count = (n::Int) -> (i = 0; while i < n; i += 1; end; i)
    @test @roundtrip f_count(5)
    @test @roundtrip f_count(0)
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
            @check "for %arg{{[0-9]+}} = 0:1:%{{.*}}"
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

@testset "type preservation" begin
    sci, _ = code_structured(Tuple{Float64}) do x::Float64
        x + 1.0
    end |> only

    # Float64 type should be preserved in entry block types
    @test !isempty(sci.entry.body)
    @test any(((_, entry),) -> entry.typ isa Type && entry.typ <: AbstractFloat, sci.entry.body)
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

@testset "for-in-range produces valid ForOp" begin
    # Native for-in-range is promoted to ForOp
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
