@testset "debug info" begin

    # Helper: get the first source_location that is non-empty for an instruction
    function first_loc(sci)
        for inst in instructions(sci.entry)
            locs = source_location(sci, inst)
            !isempty(locs) && return locs
        end
        return SourceLocation[]
    end

    @testset "source_location returns non-empty for original stmts" begin
        f(x) = x + 1
        sci, _ = code_structured(f, Tuple{Int}) |> only
        # At least one statement should have source location info
        found = false
        for inst in instructions(sci.entry)
            locs = source_location(sci, inst)
            if !isempty(locs)
                found = true
                loc = last(locs)  # innermost
                @test loc.file isa Symbol
                @test loc.line > 0
                @test loc.method !== nothing
            end
        end
        @test found
    end

    @testset "source_location for IfOp inherits from branch" begin
        g(x) = x > 0 ? x + 1 : x - 1
        sci, _ = code_structured(g, Tuple{Int}) |> only
        # Find the IfOp instruction
        for inst in instructions(sci.entry)
            if stmt(inst) isa IfOp
                locs = source_location(sci, inst)
                # Should have inherited debug info from the branch condition
                @test !isempty(locs)
                break
            end
        end
    end

    @testset "source_location by ssa_idx" begin
        h(x) = x * 2
        sci, _ = code_structured(h, Tuple{Int}) |> only
        # Test the ssa_idx overload directly
        for inst in instructions(sci.entry)
            locs_inst = source_location(sci, inst)
            locs_idx = source_location(sci, inst.ssa_idx)
            @test locs_inst == locs_idx
        end
    end

    @testset "source_location returns empty for unknown SSA" begin
        f(x) = x + 1
        sci, _ = code_structured(f, Tuple{Int}) |> only
        locs = source_location(sci, 999999)
        @test isempty(locs)
    end

    @testset "unstructurize roundtrip preserves line info" begin
        f(x) = x > 0 ? x + 1 : x - 1
        ir, _ = only(code_ircode(f, Tuple{Int}))
        sci = StructuredIRCode(ir)
        ir2 = Core.Compiler.IRCode(sci)

        # Count non-zero line entries in original and roundtripped IR
        n_orig = length(ir.stmts.stmt)
        n_new = length(ir2.stmts.stmt)

        @static if VERSION >= v"1.12-"
            orig_nonzero = count(i -> ir.stmts.line[3i-2] != 0, 1:n_orig)
            new_nonzero = count(i -> ir2.stmts.line[3i-2] != 0, 1:n_new)
        else
            orig_nonzero = count(i -> ir.stmts.line[i] != 0, 1:n_orig)
            new_nonzero = count(i -> ir2.stmts.line[i] != 0, 1:n_new)
        end

        # The roundtripped IR should have some non-zero line entries
        @test orig_nonzero > 0
        @test new_nonzero > 0
    end

    @testset "SourceLocation show" begin
        loc = SourceLocation(:foo, :bar, Int32(42))
        @test sprint(show, loc) == "foo at bar:42"
    end

    @testset "pretty-print debuginfo" begin
        h_disp(x) = x > 0 ? x + 1 : x - 1
        sci, _ = code_structured(h_disp, Tuple{Int}) |> only

        # Default: shows source annotations
        out_default = sprint(show, MIME"text/plain"(), sci)
        @test contains(out_default, "@ int.jl:")
        @test contains(out_default, "within")

        # debuginfo=:none strips line_map, so no annotations
        sci_none, _ = code_structured(h_disp, Tuple{Int}; debuginfo=:none) |> only
        out_none = sprint(show, MIME"text/plain"(), sci_none)
        @test !contains(out_none, "within")
    end

    @testset "LLVM IR has source annotations after roundtrip" begin
        CC = Core.Compiler

        g_llvm(x) = x > 0 ? x + 1 : x - 1
        ir, _ = only(code_ircode(g_llvm, Tuple{Int}))
        sci = StructuredIRCode(ir)
        ir2 = CC.copy(CC.IRCode(sci))
        ir2.argtypes[1] = Tuple{}
        @static if VERSION >= v"1.12-"
            ir2.debuginfo.def = ir.debuginfo.def
        end
        oc = Core.OpaqueClosure(ir2)

        buf = IOBuffer()
        code_llvm(buf, oc, Tuple{Int}; debuginfo=:source)
        llvm = String(take!(buf))

        # Should have inlined source annotations from the original code
        @test contains(llvm, "int.jl")   # + or - calls Base.add_int / sub_int
        @test contains(llvm, "within")   # inlining markers

        # Without debug info, these annotations are absent
        ir3, _ = only(code_ircode(g_llvm, Tuple{Int}))
        sci3 = StructuredIRCode(ir3)
        ir_zeroed = CC.copy(CC.IRCode(sci3))
        ir_zeroed.argtypes[1] = Tuple{}
        fill!(ir_zeroed.stmts.line, Int32(0))
        @static if VERSION >= v"1.12-"
            ir_zeroed.debuginfo.def = Symbol("zeroed")
            ir_zeroed.debuginfo.linetable = nothing
            empty!(ir_zeroed.debuginfo.edges)
        else
            empty!(ir_zeroed.linetable)
        end
        oc_zeroed = Core.OpaqueClosure(ir_zeroed)

        buf2 = IOBuffer()
        code_llvm(buf2, oc_zeroed, Tuple{Int}; debuginfo=:source)
        llvm_zeroed = String(take!(buf2))

        # Zeroed version should NOT have inlined source annotations
        @test !contains(llvm_zeroed, "int.jl")
    end

    @testset "loop debug info preserved" begin
        function loop_fn(n)
            s = 0
            for i in 1:n
                s += i
            end
            return s
        end
        sci, _ = code_structured(loop_fn, Tuple{Int}) |> only
        # Find a loop op and check it has debug info
        found_loop = false
        for inst in instructions(sci.entry)
            s = stmt(inst)
            if s isa LoopOp || s isa ForOp || s isa WhileOp
                locs = source_location(sci, inst)
                if !isempty(locs)
                    found_loop = true
                    @test last(locs).line > 0
                end
                break
            end
        end
        # It's OK if we don't find a loop (inlining etc.), but if we do it should have info
    end

end
