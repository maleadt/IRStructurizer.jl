#=============================================================================
 Interface Tests
 Tests for code_structured, validation, and display.
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

@testset "display: ForOp" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        acc = 0
        while i < n
            acc += i
            i += 1
        end
        return acc
    end |> only

    output = sprint(show, MIME"text/plain"(), sci)
    @test occursin("for", output)
    @test occursin("continue", output)
end

@testset "display: WhileOp" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        while n > 0
            n -= 1
        end
        return n
    end |> only

    output = sprint(show, MIME"text/plain"(), sci)
    @test occursin("while", output)
end

@testset "display: ForOp" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        acc = 0
        for i in 1:n
            acc += i
        end
        return acc
    end |> only

    output = sprint(show, MIME"text/plain"(), sci)
    @test occursin("for", output)
end

@testset "display: nested" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        acc = 0
        i = 0
        while i < n
            if i % 2 == 0
                acc += i
            end
            i += 1
        end
        return acc
    end |> only

    output = sprint(show, MIME"text/plain"(), sci)
    @test occursin("for", output)
    @test occursin("if", output)
end

end  # interface
