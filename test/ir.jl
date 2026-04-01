#=============================================================================
 IR Types & Utilities Tests
 Tests for src/ir/types.jl and src/ir/utilities.jl.
=============================================================================#

@testset "types & accessors" begin

@testset "instructions(block)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    insts = collect(instructions(sci.entry))
    @test !isempty(insts)
    @test all(i -> i isa Instruction, insts)

    # Each Instruction bundles ssa_idx, stmt, typ
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
            @test all(a -> a isa BlockArgument, body_args)
            break
        end
    end
end

@testset "terminator(block)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    @test terminator(sci.entry) === sci.entry.terminator
    @test terminator(sci.entry) isa ReturnNode
end

@testset "terminator!(block, term)" begin
    block = Block()
    @test terminator(block) === nothing

    ret = ReturnNode(SSAValue(1))
    @test terminator!(block, ret) === ret
    @test terminator(block) === ret

    y = YieldOp([SSAValue(2)])
    terminator!(block, y)
    @test terminator(block) === y
end

@testset "operands(term)" begin
    # YieldOp, ContinueOp, BreakOp → .values
    y = YieldOp([SSAValue(1), SSAValue(2)])
    @test operands(y) === y.values
    @test operands(y) == [SSAValue(1), SSAValue(2)]

    c = ContinueOp([SSAValue(3)])
    @test operands(c) === c.values

    b = BreakOp([SSAValue(4)])
    @test operands(b) === b.values

    # ConditionOp → .args
    co = ConditionOp(SSAValue(10), [SSAValue(5), SSAValue(6)])
    @test operands(co) === co.args
    @test operands(co) == [SSAValue(5), SSAValue(6)]

    # Mutation through operands
    operands(y)[1] = SSAValue(99)
    @test y.values[1] == SSAValue(99)
    operands(co)[1] = SSAValue(88)
    @test co.args[1] == SSAValue(88)
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

@testset "isempty(block)" begin
    @test isempty(Block())

    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only
    @test !isempty(sci.entry)
end

end  # types & accessors

@testset "block mutation" begin

@testset "push! / insert_before! / insert_after!" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    old_max = sci.max_ssa_idx

    # push! returns Instruction with auto-allocated SSA
    new_inst = push!(sci.entry, Expr(:call, :dummy), Int)
    @test new_inst isa Instruction
    @test new_inst.ssa_idx == old_max + 1
    @test sci.max_ssa_idx == old_max + 1

    # insert_before! / insert_after!
    insts = collect(instructions(sci.entry))
    ref = first(insts)
    before = insert_before!(sci.entry, ref, Expr(:call, :before), Int32)
    after = insert_after!(sci.entry, ref, Expr(:call, :after), Int64)
    @test before isa Instruction && after isa Instruction

    all_insts = collect(instructions(sci.entry))
    bp = findfirst(i -> i == before, all_insts)
    rp = findfirst(i -> i == ref, all_insts)
    ap = findfirst(i -> i == after, all_insts)
    @test bp < rp < ap
end

@testset "pushfirst!(block, stmt, typ)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    old_first = first(instructions(sci.entry))
    new_inst = pushfirst!(sci.entry, Expr(:call, :sentinel), Int)
    @test new_inst isa Instruction
    @test first(instructions(sci.entry)) == new_inst
    @test collect(instructions(sci.entry))[2] == old_first
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

@testset "empty!(block)" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    @test !isempty(collect(instructions(sci.entry)))
    empty!(sci.entry)
    @test isempty(collect(instructions(sci.entry)))
    # Args and terminator preserved
    @test sci.entry.terminator !== nothing
end

@testset "val in block" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        i = 0
        acc = 0
        while i < n
            acc += i
            i += 1
        end
        acc
    end |> only

    # SSAValue defined in entry block
    entry_inst = first(instructions(sci.entry))
    @test SSAValue(entry_inst) ∈ sci.entry

    # Find a loop and check its body
    loop_op = nothing
    for inst in instructions(sci.entry)
        s = stmt(inst)
        if s isa ForOp || s isa WhileOp || s isa LoopOp
            loop_op = s
            break
        end
    end
    @test loop_op !== nothing

    body = loop_op isa WhileOp ? loop_op.before : loop_op.body
    if !isempty(collect(instructions(body)))
        body_inst = first(instructions(body))
        # Body instruction is in its own block, not in entry
        @test SSAValue(body_inst) ∈ body
        @test !(SSAValue(body_inst) ∈ sci.entry)
    end

    # BlockArguments
    if !isempty(body.args)
        @test body.args[1] ∈ body
        @test !(body.args[1] ∈ sci.entry)
    end

    # Constants and Arguments are never "in" a block
    @test !(Core.Argument(1) ∈ sci.entry)
    @test !(42 ∈ sci.entry)
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
        @test new_arg isa BlockArgument
        @test new_arg.type == Float32
        @test length(arguments(op.body)) == old_n + 1
        @test arguments(op.body)[end] === new_arg
        break
    end
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
    @test before isa Instruction

    # insert_after! with SSAValue reference
    after = insert_after!(sci.entry, ref_ssaval, Expr(:call, :after_ssa), Int64)
    @test after isa Instruction

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

@testset "insert_before! with bad ref throws KeyError" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    bad_ref = Instruction(999999, nothing, Nothing, Block())
    @test_throws KeyError insert_before!(sci.entry, bad_ref, Expr(:call, :x), Int)
end

end  # block mutation

@testset "traversal" begin

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
    @test findblock(sci, Instruction(999999, nothing, Nothing, Block())) === nothing
end

@testset "reachable_terminators(block)" begin
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
            terms = reachable_terminators(op.body)
            @test !isempty(terms)
            @test any(t -> t isa ContinueOp, terms)
            break
        end
    end
end

@testset "reachable_terminators() excludes IfOp YieldOps" begin
    # LoopOp body with an IfOp that produces a result (YieldOps in branches)
    # plus a ContinueOp at the body level.
    # reachable_terminators() should return only ContinueOp, not the IfOp YieldOps.
    then_blk = Block()
    then_blk.terminator = YieldOp(Any[SSAValue(30)])
    else_blk = Block()
    else_blk.terminator = YieldOp(Any[SSAValue(31)])

    body = Block()
    a1 = BlockArgument(1, Int)
    push!(body.args, a1)
    ifop = IfOp(SSAValue(1), then_blk, else_blk)
    push!(body.body, (10, ifop, Int))
    body.terminator = ContinueOp(Any[SSAValue(40)])

    op = LoopOp(body, Any[SSAValue(100)])

    terms = reachable_terminators(op.body)
    @test length(terms) == 1
    @test terms[1] isa ContinueOp
    @test !any(t -> t isa YieldOp, terms)
end

@testset "reachable_terminators() collects BreakOp through IfOp but not YieldOp" begin
    # IfOp with one branch breaking and one yielding
    then_blk = Block()
    then_blk.terminator = BreakOp(Any[SSAValue(50)])
    else_blk = Block()
    else_blk.terminator = YieldOp(Any[SSAValue(31)])

    body = Block()
    a1 = BlockArgument(1, Int)
    push!(body.args, a1)
    ifop = IfOp(SSAValue(1), then_blk, else_blk)
    push!(body.body, (10, ifop, Int))
    body.terminator = ContinueOp(Any[SSAValue(40)])

    op = LoopOp(body, Any[SSAValue(100)])

    terms = reachable_terminators(op.body)
    @test length(terms) == 2  # ContinueOp + BreakOp
    @test any(t -> t isa ContinueOp, terms)
    @test any(t -> t isa BreakOp, terms)
    @test !any(t -> t isa YieldOp, terms)
end

@testset "WhileOp after-block YieldOp IS collected" begin
    before = Block()
    before.terminator = ConditionOp(SSAValue(1), Any[])
    after = Block()
    after.terminator = YieldOp(Any[])

    op = WhileOp(before, after, Any[])

    # The after-block's YieldOp is a top-level terminator, not nested in an IfOp
    terms_after = reachable_terminators(op.after)
    @test length(terms_after) == 1
    @test terms_after[1] isa YieldOp

    terms_before = reachable_terminators(op.before)
    @test length(terms_before) == 1
    @test terms_before[1] isa ConditionOp
end

@testset "walk(f, root)" begin
    # Build a simple IR: entry with an IfOp containing instructions
    sci, _ = code_structured(x -> x > 0 ? x + 1 : x - 1, Tuple{Int}) |> only

    # Preorder: collect all instructions
    pre_insts = Instruction[]
    walk(sci) do inst, block
        push!(pre_insts, inst)
        return :advance
    end
    @test !isempty(pre_insts)

    # Postorder: collect all instructions
    post_insts = Instruction[]
    walk(sci; order=:postorder) do inst, block
        push!(post_insts, inst)
        return :advance
    end
    @test length(post_insts) == length(pre_insts)
    @test Set(i.ssa_idx for i in post_insts) == Set(i.ssa_idx for i in pre_insts)

    # In preorder, the IfOp should come before instructions inside it
    ifop_idx = findfirst(i -> stmt(i) isa IfOp, pre_insts)
    @test ifop_idx !== nothing
    # Instructionructions after the IfOp in preorder should include nested ones
    @test length(pre_insts) > ifop_idx

    # In postorder, the IfOp should come after instructions inside it
    ifop_idx_post = findfirst(i -> stmt(i) isa IfOp, post_insts)
    @test ifop_idx_post > 1  # nested instructions come first

    # Skip: don't recurse into IfOp
    skip_insts = Instruction[]
    walk(sci) do inst, block
        push!(skip_insts, inst)
        stmt(inst) isa IfOp && return :skip
        return :advance
    end
    @test length(skip_insts) < length(pre_insts)

    # Interrupt: stop after first instruction
    first_only = Instruction[]
    walk(sci) do inst, block
        push!(first_only, inst)
        return :interrupt
    end
    @test length(first_only) == 1

    # Nothing return treated as :advance
    nothing_insts = Instruction[]
    walk(sci) do inst, block
        push!(nothing_insts, inst)
        nothing
    end
    @test length(nothing_insts) == length(pre_insts)

    # Invalid order
    @test_throws ArgumentError walk((inst, block) -> :advance, sci; order=:invalid)
end

@testset "empty block edge cases" begin
    block = Block()

    @test isempty(collect(instructions(block)))
    @test isempty(uses(block).index)
    @test isempty(reachable_terminators(block))
    @test isempty(block)
end

end  # traversal

@testset "use tracking" begin

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

@testset "users(block, val)" begin
    # users() returns Instructions (owning operations), not UseRefs (use-sites)
    block = Block()
    push!(block.body, (1, Expr(:call, GlobalRef(Base, :+), SSAValue(0), SSAValue(0)), Int))
    push!(block.body, (2, Expr(:call, GlobalRef(Base, :*), SSAValue(1), SSAValue(0)), Int))

    # SSAValue(0) is used in both instructions
    u = users(block, SSAValue(0))
    @test length(u) == 2
    @test all(inst -> inst isa Instruction, u)
    @test Set(inst.ssa_idx for inst in u) == Set([1, 2])

    # SSAValue(1) is only used in instruction 2
    u1 = users(block, SSAValue(1))
    @test length(u1) == 1
    @test u1[1].ssa_idx == 2

    # SSAValue(99) is not used anywhere
    @test isempty(users(block, SSAValue(99)))
end

@testset "users with nested control flow" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        acc = 0
        for i in 1:n
            acc += i
        end
        return acc
    end |> only

    # Argument(2) (n) should have at least one user instruction
    u = users(sci.entry, Core.Argument(2))
    @test !isempty(u)
    @test all(inst -> inst isa Instruction, u)
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

end  # use tracking

@testset "loop carries" begin

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
        @test body_arg(cr) isa BlockArgument
        found = true
        break
    end
    @test found
end

@testset "carries filter!" begin
    # Build a ForOp with 2 carries, filter to keep only the first
    body = Block()
    iv = BlockArgument(1, Int)
    a1 = BlockArgument(2, Float64)
    a2 = BlockArgument(3, Float64)
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
    iv = BlockArgument(1, Int)
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

@testset "deleteat!(carries, indices)" begin
    body = Block()
    iv = BlockArgument(1, Int)
    a1 = BlockArgument(2, Float64)
    a2 = BlockArgument(3, Float64)
    a3 = BlockArgument(4, Float64)
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

@testset "init_value! and term_value! setters" begin
    body = Block()
    iv = BlockArgument(1, Int)
    a1 = BlockArgument(2, Float64)
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

@testset "push!(carries) doesn't pollute IfOp YieldOps" begin
    # LoopOp body with IfOp producing a result via YieldOps + ContinueOp
    then_blk = Block()
    then_blk.terminator = YieldOp(Any[SSAValue(30)])
    else_blk = Block()
    else_blk.terminator = YieldOp(Any[SSAValue(31)])

    body = Block()
    a1 = BlockArgument(1, Int)
    push!(body.args, a1)
    ifop = IfOp(SSAValue(1), then_blk, else_blk)
    push!(body.body, (10, ifop, Int))
    body.terminator = ContinueOp(Any[SSAValue(40)])

    op = LoopOp(body, Any[SSAValue(100)])

    # Wrap in SCI so root() works
    entry = Block()
    push!(entry.body, (11, op, Nothing))
    sci = StructuredIRCode(Any[], Any[], entry, 11)
    entry.parent = sci
    body.parent = entry
    then_blk.parent = body
    else_blk.parent = body

    c = carries(op)
    @test length(c) == 1

    # push! should thread through ContinueOp but NOT the IfOp YieldOps
    push!(c, SSAValue(200), Float64)
    @test length(body.terminator.values) == 2  # ContinueOp got the new carry
    @test length(then_blk.terminator.values) == 1  # YieldOp untouched
    @test length(else_blk.terminator.values) == 1  # YieldOp untouched
end

@testset "carries for WhileOp" begin
    before = Block()
    after = Block()
    a1_before = BlockArgument(1, Int)
    a2_before = BlockArgument(2, Float64)
    push!(before.args, a1_before)
    push!(before.args, a2_before)
    before.terminator = ConditionOp(SSAValue(1), Any[a1_before, a2_before])

    a1_after = BlockArgument(1, Int)
    a2_after = BlockArgument(2, Float64)
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
    a1 = BlockArgument(1, Int)
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

@testset "after_arg(carry_ref) for WhileOp" begin
    # Build a WhileOp with carries
    before = Block()
    after = Block()
    before_arg = BlockArgument(100, Int)
    after_blk_arg = BlockArgument(101, Int)
    push!(before.args, before_arg)
    push!(after.args, after_blk_arg)
    before.terminator = ConditionOp(SSAValue(1), [before_arg])
    after.terminator = YieldOp([after_blk_arg])
    op = WhileOp(before, after, IRStructurizer.IRValue[SSAValue(50)])

    sci = StructuredIRCode(Any[], Any[], Block(), 200)
    push!(sci.entry, 10, op, Nothing)

    c = carries(op)
    @test length(c) == 1
    cr = c[1]
    @test body_arg(cr) === before_arg
    @test after_arg(cr) === after_blk_arg
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
    push!(body.args, BlockArgument(1, Int))  # 1 user block arg
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

end  # loop carries

@testset "expression inspection" begin

@testset "resolve_call" begin
    using IRStructurizer: resolve_call

    # Use a real SCI to get a block with type information
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only
    block = sci.entry

    # :call expression with GlobalRef
    expr_call = Expr(:call, GlobalRef(Base, :+), SSAValue(1), SSAValue(2))
    result = resolve_call(block, expr_call)
    @test result !== nothing
    func, operands = result
    @test func === Base.:+
    @test length(operands) == 2
    @test operands[1] == SSAValue(1)

    # :invoke expression
    mi = first(methods(+, (Int, Int)))
    expr_invoke = Expr(:invoke, mi, GlobalRef(Base, :+), SSAValue(1), SSAValue(2))
    result2 = resolve_call(block, expr_invoke)
    @test result2 !== nothing
    func2, operands2 = result2
    @test func2 === Base.:+
    @test length(operands2) == 2

    # Non-call returns nothing
    @test resolve_call(block, 42) === nothing
    @test resolve_call(block, Expr(:new, :Foo)) === nothing

    # Instruction overload
    inst = Instruction(1, expr_call, Int, Block())
    result3 = resolve_call(block, inst)
    @test result3 !== nothing
    @test first(result3) === Base.:+

    # SSAValue callee resolved via singleton type
    # Build a :call where args[1] is an SSAValue whose type is a singleton function
    # Find an instruction in the SCI that is a call, use its SSA index as a fake callee
    # to test the type-based resolution path
    callee_ssa_idx = nothing
    for inst in instructions(block)
        s = stmt(inst)
        s isa Expr && s.head === :call || continue
        # This SSA defines a call result; create a synthetic :call that uses
        # a different SSA (one typed as a singleton function) as the callee.
        # Look for a GlobalRef statement whose type is a singleton function type.
        if s.args[1] isa GlobalRef
            callee_ssa_idx = inst.ssa_idx
            break
        end
    end
    # Construct a synthetic indirect call: insert a GlobalRef as a regular
    # statement, then reference it via SSAValue as the callee.
    # Instead, we can test resolve_callee directly on an SSAValue.
    # Find any instruction with a singleton function type (e.g., typeof(+)).
    using IRStructurizer: resolve_callee
    for inst in instructions(block)
        T = value_type(inst)
        T === nothing && continue
        singleton = Core.Compiler.singleton_type(T)
        singleton === nothing && continue
        # This SSA value has a singleton type — resolve_callee should find it
        @test resolve_callee(block, SSAValue(inst)) === singleton
        break
    end
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

    # Instruction overloads
    inst = Instruction(1, expr_call, Int, Block())
    @test iscall(inst)
    @test callee(inst) == GlobalRef(Base, :+)
    @test length(callargs(inst)) == 2
end

@testset "callee/callargs error on non-call" begin
    using IRStructurizer: callee, callargs
    @test_throws ArgumentError callee(Expr(:new, :Foo))
    @test_throws ArgumentError callargs(Expr(:new, :Foo))
end

end  # expression inspection

@testset "value_type(block, val)" begin

@testset "SSAValue in same block" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    inst = first(instructions(sci.entry))
    typ = value_type(sci.entry, SSAValue(inst))
    @test typ !== nothing
    @test typ == value_type(inst)
end

@testset "SSAValue from parent block" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x > 0 ? x + 1 : x - 1
    end |> only

    # Find an SSAValue defined in the entry block and look it up from a nested block
    for inst in instructions(sci.entry)
        if stmt(inst) isa IfOp
            ifop = stmt(inst)
            then_blk = ifop.then_region
            # The condition SSAValue is defined in the entry block
            cond = ifop.condition
            if cond isa SSAValue
                typ = value_type(then_blk, cond)
                @test typ !== nothing
            end
            break
        end
    end
end

@testset "BlockArgument" begin
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
        op isa IRStructurizer.ControlFlowOp || continue
        for blk in blocks(op)
            if !isempty(arguments(blk))
                arg = first(arguments(blk))
                @test value_type(blk, arg) == arg.type
                found = true
                break
            end
        end
        found && break
    end
    @test found
end

@testset "Argument" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    # Argument(1) is the function itself, Argument(2) is x::Int
    typ = value_type(sci.entry, Core.Argument(2))
    @test typ !== nothing
end

@testset "constant" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    @test value_type(sci.entry, 42) == Int
    @test value_type(sci.entry, 3.14) == Float64
    @test value_type(sci.entry, true) == Bool
end

@testset "unknown SSAValue" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    @test value_type(sci.entry, SSAValue(999999)) === nothing
end

end  # value_type(block, val)

@testset "operands(op::ControlFlowOp)" begin

@testset "IfOp" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x > 0 ? x + 1 : x - 1
    end |> only

    for inst in instructions(sci.entry)
        if stmt(inst) isa IfOp
            ops = operands(stmt(inst))
            @test length(ops) == 1
            @test ops[1] isa SSAValue  # the condition
            break
        end
    end
end

@testset "ForOp" begin
    sci, _ = code_structured(Tuple{Int}) do n::Int
        s = 0
        i = 1
        while i <= n
            s += i
            i += 1
        end
        s
    end |> only

    found = false
    walk(sci) do inst, block
        if stmt(inst) isa ForOp
            op = stmt(inst)
            ops = operands(op)
            # lower, upper, step, plus any init_values
            @test length(ops) >= 3
            found = true
        end
        :advance
    end
    @test found
end

@testset "WhileOp" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        while x > 0
            x -= 1
        end
        x
    end |> only

    found = false
    walk(sci) do inst, block
        if stmt(inst) isa WhileOp
            op = stmt(inst)
            ops = operands(op)
            # init_values only (WhileOp has no explicit bounds)
            @test ops isa Vector
            @test length(ops) == length(op.init_values)
            # operands returns a copy, not a reference
            @test ops !== op.init_values
            found = true
        end
        :advance
    end
    @test found
end

@testset "LoopOp" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        while true
            x -= 1
            x <= 0 && break
        end
        x
    end |> only

    found = false
    walk(sci) do inst, block
        if stmt(inst) isa LoopOp
            op = stmt(inst)
            ops = operands(op)
            @test ops isa Vector
            @test length(ops) == length(op.init_values)
            found = true
        end
        :advance
    end
    @test found
end

end  # operands(op::ControlFlowOp)

@testset "operands(block, inst)" begin

@testset "call expression" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    # Find a call instruction (first instruction may not be an Expr on all Julia versions)
    found = false
    for inst in instructions(sci.entry)
        if iscall(inst)
            ops = operands(sci.entry, inst)
            @test ops isa Vector
            @test !isempty(ops)
            found = true
            break
        end
    end
    @test found
end

@testset "non-call statement" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    # Insert a non-Expr statement to test operands returns empty
    inst = push!(sci.entry, 42, Int)
    ops = operands(sci.entry, inst)
    @test isempty(ops)
end

end  # operands(block, inst)

@testset "def" begin

@testset "basic lookup" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    # First instruction defines some SSAValue
    inst1 = first(instructions(sci.entry))
    result = def(sci, SSAValue(inst1.ssa_idx))
    @test result !== nothing
    @test result.ssa_idx == inst1.ssa_idx
    @test block(result) === sci.entry
end

@testset "nested block" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x > 0 ? x + 1 : x - 1
    end |> only

    # Find an SSAValue defined inside a nested block (then/else region)
    for inst in instructions(sci.entry)
        if stmt(inst) isa IfOp
            op = stmt(inst)
            inner_inst = first(instructions(op.then_region))
            result = def(sci, SSAValue(inner_inst.ssa_idx))
            @test result !== nothing
            @test result.ssa_idx == inner_inst.ssa_idx
            @test block(result) === op.then_region
            break
        end
    end
end

@testset "not found" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x + 1
    end |> only

    @test def(sci, SSAValue(999999)) === nothing
end

@testset "defs" begin
    sci, _ = code_structured(Tuple{Int}) do x::Int
        x > 0 ? x + 1 : x - 1
    end |> only

    idx = defs(sci)

    # All instructions are in the index
    count = 0
    walk(sci) do inst, blk
        result = def(idx, SSAValue(inst.ssa_idx))
        @test result !== nothing
        @test result.ssa_idx == inst.ssa_idx
        count += 1
        :advance
    end
    @test count == length(idx.map)

    # Missing SSAValue
    @test def(idx, SSAValue(999999)) === nothing
end

end  # def
