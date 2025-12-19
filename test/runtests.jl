using Test

using IRStructurizer
using IRStructurizer: Block, IfOp, ForOp, WhileOp, LoopOp, YieldOp, ContinueOp, BreakOp,
                      ControlFlowOp, validate_scf

@testset "IRStructurizer" verbose=true begin

@testset "interface" begin

@testset "low-level API" begin
    g(x) = x > 0 ? x + 1 : x - 1
    ci, _ = only(code_typed(g, (Int,)))

    # Create flat, then structurize
    sci = StructuredCodeInfo(ci)
    @test !any(item -> item isa IfOp, sci.entry.body)

    structurize!(sci)
    @test any(item -> item isa IfOp, sci.entry.body)

    # code_structured does both steps
    sci2 = code_structured(g, Tuple{Int})
    @test any(item -> item isa IfOp, sci2.entry.body)
end

@testset "validation: UnstructuredControlFlowError" begin
    # Create unstructured view and verify validation fails
    g(x) = x > 0 ? x + 1 : x - 1
    ci, _ = only(code_typed(g, (Int,)))

    # Flat view has GotoIfNot
    sci = StructuredCodeInfo(ci)
    gotoifnot_idx = findfirst(s -> s isa Core.GotoIfNot, ci.code)
    @test gotoifnot_idx !== nothing
    @test gotoifnot_idx in sci.entry.body

    # Validation should throw
    @test_throws UnstructuredControlFlowError validate_scf(sci)

    # After structurize!, validation passes
    structurize!(sci)
    @test gotoifnot_idx ∉ sci.entry.body
    validate_scf(sci)  # Should not throw
end

@testset "display output format" begin
    # Verify display shows proper structure
    branch_test(x::Bool) = x ? 1 : 2

    sci = code_structured(branch_test, Tuple{Bool})

    io = IOBuffer()
    show(io, MIME"text/plain"(), sci)
    output = String(take!(io))

    @test occursin("StructuredCodeInfo", output)
    @test occursin("if ", output)
    @test occursin("else", output)
    @test occursin("return", output)

    # Compact display
    io = IOBuffer()
    show(io, sci)
    output = String(take!(io))

    @test occursin("StructuredCodeInfo", output)
    @test occursin("stmts", output)
end

end

@testset "patterns" begin

@testset "straight-line code" begin
    # Simple function: single addition
    f(x) = x + 1

    sci = code_structured(f, Tuple{Int})
    @test sci isa StructuredCodeInfo

    # Entry block: one statement (the add), no control flow ops
    @test length(sci.entry.body) == 1
    @test sci.entry.body[1] isa Int
    @test sci.entry.terminator isa Core.ReturnNode

    # Multiple operations: (x + y) * (x - y)
    g(x, y) = (x + y) * (x - y)

    sci = code_structured(g, Tuple{Int, Int})
    @test sci isa StructuredCodeInfo

    # Entry block: 3 statements (add, sub, mul), no control flow ops
    @test length(sci.entry.body) == 3
    @test all(item isa Int for item in sci.entry.body)
    @test sci.entry.terminator isa Core.ReturnNode
end

@testset "if-then-else: simple ternary" begin
    # Simplest case: Bool condition, constant returns
    # Produces: [IfOp] with empty branches that just return
    branch_test(x::Bool) = x ? 1 : 2

    sci = code_structured(branch_test, Tuple{Bool})
    @test sci isa StructuredCodeInfo

    # Entry: exactly one IfOp, no statements
    @test length(sci.entry.body) == 1
    @test sci.entry.body[1] isa IfOp

    if_op = sci.entry.body[1]

    # Condition is the first argument (the Bool)
    @test if_op.condition isa Core.Argument
    @test if_op.condition.n == 2  # arg 1 is #self#

    # Then branch: empty body, returns constant 1
    @test isempty(if_op.then_block.body)
    @test if_op.then_block.terminator isa Core.ReturnNode
    @test if_op.then_block.terminator.val == 1

    # Else branch: empty body, returns constant 2
    @test isempty(if_op.else_block.body)
    @test if_op.else_block.terminator isa Core.ReturnNode
    @test if_op.else_block.terminator.val == 2
end

@testset "if-then-else: with comparison" begin
    # Comparison before branch, computation in branches
    # Produces: [stmt (comparison), IfOp]
    cmp_branch(x::Int) = x > 0 ? x : -x

    sci = code_structured(cmp_branch, Tuple{Int})
    @test sci isa StructuredCodeInfo

    # Entry: one stmt (comparison), then IfOp
    @test length(sci.entry.body) == 2
    @test sci.entry.body[1] isa Int  # comparison stmt
    @test sci.entry.body[2] isa IfOp

    if_op = sci.entry.body[2]

    # Condition references the comparison result
    @test if_op.condition isa Core.SSAValue
    @test if_op.condition.id == sci.entry.body[1]

    # Then branch: returns x (the argument)
    @test if_op.then_block.terminator isa Core.ReturnNode

    # Else branch: has negation, then returns
    @test if_op.else_block.terminator isa Core.ReturnNode
end

@testset "if-then-else: with computation in branches" begin
    # Both branches do computation before returning
    compute_branch(x::Int) = x > 0 ? x + 1 : x - 1

    sci = code_structured(compute_branch, Tuple{Int})
    @test sci isa StructuredCodeInfo

    # Entry: comparison stmt, then IfOp
    @test length(sci.entry.body) == 2
    @test sci.entry.body[1] isa Int
    @test sci.entry.body[2] isa IfOp

    if_op = sci.entry.body[2]

    # Then branch: one stmt (addition), then return
    @test length(if_op.then_block.body) == 1
    @test if_op.then_block.body[1] isa Int
    @test if_op.then_block.terminator isa Core.ReturnNode

    # Else branch: one stmt (subtraction), then return
    @test length(if_op.else_block.body) == 1
    @test if_op.else_block.body[1] isa Int
    @test if_op.else_block.terminator isa Core.ReturnNode
end

@testset "if-then-else: early return pattern" begin
    # if-else where one branch returns early, other continues
    function early_return(x::Int, y::Int)
        if x > y
            return y * x
        end
        y - x
    end

    sci = code_structured(early_return, Tuple{Int, Int})
    @test sci isa StructuredCodeInfo

    # Entry: [comparison_stmt, IfOp]
    @test length(sci.entry.body) == 2
    @test sci.entry.body[1] isa Int
    @test sci.entry.body[2] isa IfOp

    if_op = sci.entry.body[2]

    # Both branches terminate with return
    @test if_op.then_block.terminator isa Core.ReturnNode
    @test if_op.else_block.terminator isa Core.ReturnNode
end

@testset "while-loop: countdown pattern" begin
    # Decrementing loop - may be ForOp or WhileOp depending on detection
    function countdown(n::Int)
        while n > 0
            n -= 1
        end
        return n
    end

    sci = code_structured(countdown, Tuple{Int})
    @test sci isa StructuredCodeInfo

    # Entry should have items, last is a loop op
    @test !isempty(sci.entry.body)
    loop_op = sci.entry.body[end]
    @test loop_op isa Union{ForOp, WhileOp, LoopOp}
end

@testset "while-loop: spinloop pattern" begin
    # While loop that is NOT a for-loop (no increment pattern)
    function spinloop(flag::Int)
        while flag != 0
            # spin - no body operations, just condition check
        end
        return flag
    end

    sci = code_structured(spinloop, Tuple{Int})
    @test sci isa StructuredCodeInfo

    # Entry: [WhileOp] - no setup statements
    @test length(sci.entry.body) == 1
    @test sci.entry.body[1] isa WhileOp

    while_op = sci.entry.body[1]

    # Condition is the != comparison
    @test while_op.condition isa Core.SSAValue

    # No loop-carried values (flag is just re-read each iteration)
    @test isempty(while_op.init_values)
    @test isempty(while_op.body.args)

    # Body has the condition computation statements
    @test !isempty(while_op.body.body)
    @test all(item isa Int for item in while_op.body.body)

    # Terminates with ContinueOp
    @test while_op.body.terminator isa ContinueOp
end

@testset "for-loop: simple counting loop" begin
    # Simple while loop that matches ForOp pattern:
    # - Induction variable starts at 0
    # - Increments by 1
    # - Condition is i < n
    function count_loop(n::Int)
        i = 0
        acc = 0
        while i < n
            acc += i
            i += 1
        end
        return acc
    end

    sci = code_structured(count_loop, Tuple{Int})
    @test sci isa StructuredCodeInfo

    # Entry: [init_stmt, ForOp]
    @test length(sci.entry.body) == 2
    @test sci.entry.body[1] isa Int
    @test sci.entry.body[2] isa ForOp

    for_op = sci.entry.body[2]

    # Bounds: 0 to n, step 1
    @test for_op.lower == 0
    @test for_op.upper isa Core.Argument
    @test for_op.step == 1

    # Body has block args: [induction_var, accumulator]
    @test length(for_op.body.args) == 2

    # Body terminates with ContinueOp (not YieldOp)
    @test for_op.body.terminator isa ContinueOp

    # Loop produces one result (the final accumulator value)
    @test length(for_op.result_vars) == 1
end

@testset "nested loops" begin
    # Two nested counting loops
    function nested_count(n::Int, m::Int)
        acc = 0
        i = 0
        while i < n
            j = 0
            while j < m
                acc += 1
                j += 1
            end
            i += 1
        end
        return acc
    end

    sci = code_structured(nested_count, Tuple{Int, Int})
    @test sci isa StructuredCodeInfo

    # Entry: [init_stmt, outer_ForOp]
    @test length(sci.entry.body) == 2
    @test sci.entry.body[1] isa Int
    @test sci.entry.body[2] isa ForOp

    outer_loop = sci.entry.body[2]

    # Outer body: [init_stmt, inner_ForOp]
    @test length(outer_loop.body.body) == 2
    @test outer_loop.body.body[1] isa Int
    @test outer_loop.body.body[2] isa ForOp

    inner_loop = outer_loop.body.body[2]

    # Inner loop has its own structure
    @test inner_loop.body.terminator isa ContinueOp
end

end

@testset "loop exit: no duplicated statements" begin
    # Regression test: statements after loop should not be duplicated
    function loop_then_compute(x::Int)
        i = 0
        while i < x
            i += 1
        end
        # This should appear exactly once
        result = i * 2
        return result
    end

    sci = code_structured(loop_then_compute, Tuple{Int})
    @test sci isa StructuredCodeInfo

    # Collect all statement indices in entry block
    stmt_indices = filter(item -> item isa Int, sci.entry.body)

    # No duplicates
    @test length(stmt_indices) == length(unique(stmt_indices))

    # Check display output: mul_int should appear exactly once
    io = IOBuffer()
    show(io, MIME"text/plain"(), sci)
    output = String(take!(io))
    @test count("mul_int", output) == 1
end

@testset "type preservation" begin
    f(x::Float64) = x + 1.0

    sci = code_structured(f, Tuple{Float64})
    @test sci isa StructuredCodeInfo

    # Float64 type should be preserved in ssavaluetypes
    @test !isempty(sci.code.ssavaluetypes)
    @test any(t -> t isa Type && t <: AbstractFloat, sci.code.ssavaluetypes)
end

@testset "multiple arguments" begin
    # Different argument types
    h(x::Int, y::Float64) = x + y

    sci = code_structured(h, Tuple{Int, Float64})
    @test sci isa StructuredCodeInfo
    @test sci.entry.terminator isa Core.ReturnNode
end

end  # @testset "IRStructurizer"
