# Tests for type preservation across control flow constructs (Issue #3)

struct CustomPoint
    x::Float32
    y::Float64
end

struct Container{T}
    value::T
end

@testset "type preservation" begin
    # Helper to check that every statement in a block and its nested blocks
    # has a valid type, and CF op result types are tuples or Nothing.
    function check_block_types(blk::Block)
        for (idx, entry) in blk.body
            @test entry.type isa Type
            stmt = entry.stmt
            if stmt isa IfOp
                @test entry.type <: Tuple || entry.type === Nothing
                check_block_types(stmt.then_region)
                check_block_types(stmt.else_region)
            elseif stmt isa ForOp
                @test entry.type <: Tuple || entry.type === Nothing
                @test stmt.iv_arg.type isa Type
                check_block_types(stmt.body)
            elseif stmt isa WhileOp
                @test entry.type <: Tuple || entry.type === Nothing
                check_block_types(stmt.before)
                check_block_types(stmt.after)
            elseif stmt isa LoopOp
                @test entry.type <: Tuple || entry.type === Nothing
                for arg in stmt.body.args
                    @test arg.type isa Type
                end
                check_block_types(stmt.body)
            elseif stmt isa TryOp
                @test entry.type <: Tuple || entry.type === Nothing
                check_block_types(stmt.body)
                if stmt.handler !== nothing
                    check_block_types(stmt.handler)
                end
            end
        end
    end

    @testset "straight-line arithmetic and composite types" begin
        function straight_types(a::Float32, b::Float64, c::Int32, p::CustomPoint)
            x1 = a + Float32(c)
            x2 = b * Float64(a)
            x3 = CustomPoint(x1, x2 + p.y)
            return (x1, x2, x3, p.x)
        end
        (ir, ret_type), = code_ircode(straight_types, (Float32, Float64, Int32, CustomPoint))
        sci = StructuredIRCode(ir)
        check_block_types(sci.entry)
        pt = CustomPoint(1.5f0, 2.5)
        res = execute(sci, 2.0f0, 3.0, Int32(4), pt)
        expected = straight_types(2.0f0, 3.0, Int32(4), pt)
        @test res === expected
        @test typeof(res) === typeof(expected)
    end

    @testset "IfOp branch type preservation" begin
        function if_types(cond::Bool, a::Float32, b::Float32, p1::CustomPoint, p2::CustomPoint)
            if cond
                r1 = a + b
                r2 = p1
            else
                r1 = a - b
                r2 = p2
            end
            return (r1, r2.x, r2.y)
        end
        (ir, ret_type), = code_ircode(if_types, (Bool, Float32, Float32, CustomPoint, CustomPoint))
        sci = StructuredIRCode(ir)
        check_block_types(sci.entry)
        p1 = CustomPoint(1.0f0, 10.0)
        p2 = CustomPoint(2.0f0, 20.0)
        for cond in (true, false)
            res = execute(sci, cond, 3.0f0, 4.0f0, p1, p2)
            expected = if_types(cond, 3.0f0, 4.0f0, p1, p2)
            @test res === expected
            @test typeof(res) === typeof(expected)
        end
    end

    @testset "ForOp type preservation with varied IV and carry types" begin
        # Float64 carry with Int32 IV
        function for_carry_types(n::Int32, init::Float64)
            acc = init
            for i in Int32(1):n
                acc += Float64(i) * 0.5
            end
            return acc
        end
        (ir, ret_type), = code_ircode(for_carry_types, (Int32, Float64))
        sci = StructuredIRCode(ir)
        check_block_types(sci.entry)
        @test count_stmts(sci.entry, x -> x isa ForOp) == 1
        res = execute(sci, Int32(5), 10.0)
        expected = for_carry_types(Int32(5), 10.0)
        @test res === expected
        @test typeof(res) === typeof(expected)

        # Composite carry type in ForOp
        function for_struct_carry(n::Int, pt::CustomPoint)
            cur = pt
            for i in 1:n
                cur = CustomPoint(cur.x + Float32(i), cur.y + Float64(i))
            end
            return cur
        end
        (ir, ret_type), = code_ircode(for_struct_carry, (Int, CustomPoint))
        sci = StructuredIRCode(ir)
        check_block_types(sci.entry)
        pt = CustomPoint(0.0f0, 0.0)
        res = execute(sci, 4, pt)
        expected = for_struct_carry(4, pt)
        @test res === expected
        @test typeof(res) === typeof(expected)
    end

    @testset "WhileOp type preservation" begin
        function while_types(n::Int32, start::Float32)
            i = Int32(0)
            val = start
            while i < n
                val *= 1.5f0
                i += Int32(1)
            end
            return (i, val)
        end
        (ir, ret_type), = code_ircode(while_types, (Int32, Float32))
        sci = StructuredIRCode(ir)
        check_block_types(sci.entry)
        res = execute(sci, Int32(4), 2.0f0)
        expected = while_types(Int32(4), 2.0f0)
        @test res === expected
        @test typeof(res) === typeof(expected)
    end

    @testset "LoopOp type preservation with early exit" begin
        function loop_early_exit(arr::Vector{Float64}, threshold::Float64)
            s = 0.0
            i = 1
            while i <= length(arr)
                v = arr[i]
                if v > threshold
                    break
                end
                s += v
                i += 1
            end
            return (s, i)
        end
        (ir, ret_type), = code_ircode(loop_early_exit, (Vector{Float64}, Float64))
        sci = StructuredIRCode(ir)
        check_block_types(sci.entry)
        data = [1.0, 2.5, 5.0, 10.0]
        res = execute(sci, data, 4.0)
        expected = loop_early_exit(data, 4.0)
        @test res === expected
        @test typeof(res) === typeof(expected)
    end

    @testset "nested control flow type preservation" begin
        function nested_types(cond::Bool, n::Int, base::Float32)
            acc = base
            if cond
                for i in 1:n
                    if i % 2 == 0
                        acc += Float32(i)
                    else
                        acc -= Float32(i) * 0.5f0
                    end
                end
            else
                j = 0
                while j < n
                    acc += Float32(j) * 2.0f0
                    j += 1
                end
            end
            return acc
        end
        (ir, ret_type), = code_ircode(nested_types, (Bool, Int, Float32))
        sci = StructuredIRCode(ir)
        check_block_types(sci.entry)
        for cond in (true, false)
            res = execute(sci, cond, 6, 10.0f0)
            expected = nested_types(cond, 6, 10.0f0)
            @test res === expected
            @test typeof(res) === typeof(expected)
        end
    end
end
