module UseIdentityTests
using Test, IRStructurizer
using IRStructurizer: Block
using Core: SSAValue, ReturnNode

mutable struct OpaqueLiteral
    value::Int
end
Base.hash(::OpaqueLiteral, ::UInt) = error("IR indexing must not hash user operands")
Base.:(==)(::OpaqueLiteral, ::OpaqueLiteral) = error("IR indexing must not compare user operands")

@testset "operand identity" begin
    @testset "unhashable operands and replacements" begin
        a = OpaqueLiteral(1)
        b = OpaqueLiteral(1)
        replacement = OpaqueLiteral(2)
        block = Block()
        push!(block.body, (1, Expr(:call, identity, a), OpaqueLiteral))
        push!(block.body, (2, Expr(:call, identity, b), OpaqueLiteral))
        block.terminator = ReturnNode(a)

        index = uses(block)
        @test length(index[a]) == 2
        @test length(index[b]) == 1
        @test length(uses(block, a)) == 2
        @test length(users(block, a)) == 1

        replace_uses!(block, a, replacement)
        @test isempty(uses(block, a))
        @test length(uses(block, replacement)) == 2
        @test block.body.stmts[2].args[2] === b
        @test block.terminator.val === replacement
    end

    @testset "equal mutable constants remain distinct" begin
        a = [1, 2]
        b = [1, 2]
        replacement = [3, 4]
        block = Block()
        push!(block.body, (1, Expr(:call, identity, a), Vector{Int}))
        push!(block.body, (2, Expr(:call, identity, b), Vector{Int}))

        index = uses(block)
        @test length(index[a]) == 1
        @test length(index[b]) == 1
        @test length(uses(block, a)) == 1
        @test length(users(block, a)) == 1

        replace_uses!(block, a, replacement)
        @test block.body.stmts[1].args[2] === replacement
        @test block.body.stmts[2].args[2] === b

        # Mutating a literal cannot invalidate the compiler's index key.
        b[1] = 7
        @test length(index[b]) == 1
    end

    @testset "SSA normalization and numeric literal types" begin
        block = Block()
        push!(block.body, (1, Expr(:call, identity, 1), Int))
        push!(block.body, (2, Expr(:call, identity, 1.0), Float64))
        push!(block.body, (3, Expr(:call, tuple, SSAValue(1), SSAValue(2)), Tuple{Int, Float64}))
        block.terminator = ReturnNode(SSAValue(3))

        index = uses(block)
        @test length(index[1]) == 1
        @test length(index[1.0]) == 1
        @test length(uses(block, 1)) == 1
        @test length(uses(block, 1.0)) == 1
        inst = first(instructions(block))
        @test index[inst] === index[SSAValue(1)]
        @test length(index[SSAValue(1)]) == 1
        @test length(index[SSAValue(3)]) == 1

        replace_uses!(block, 1, 2)
        @test block.body.stmts[1].args[2] === 2
        @test block.body.stmts[2].args[2] === 1.0
    end
end
end
