#=============================================================================
 Mutate-then-lift CFG normalization (src/structurize/multiplex.jl).

 M1 foundation: the explicit-edge mutable form (`ingest`/`emit`) must rebuild an
 IRCode that is faithful enough to (a) execute identically and (b) re-structurize
 identically — `emit(ingest(ir))` is the no-mutation identity that M2/M3 build on.
 The EdgeMultiplexer unit tests then check the mux primitive on synthetic
 multi-entry CFGs.
=============================================================================#

const CCx = Core.Compiler
using IRStructurizer: ingest, emit, MCFG, MBlock, MEdge, MGoto, MCondBr, MReturn,
                      EdgeRef, single_entry_mux!, edge_of
using Core: Argument, GotoNode, GotoIfNot, ReturnNode, PhiNode, SSAValue

# Execute a raw IRCode via OpaqueClosure (mirrors `execute` for SCIs).
function exec_ir(ir, args...)
    ir = CCx.copy(ir)
    ir.argtypes[1] = Tuple{}
    @static if VERSION >= v"1.12-"
        ir.debuginfo.def = Symbol("roundtrip")
    end
    return Core.OpaqueClosure(ir)(args...)
end

# emit(ingest(ir)) executes identically to direct call.
function rt_identity(f, args...)
    ir, _ = only(code_ircode(f, Tuple{map(typeof, args)...}))
    ir2 = emit(ingest(ir))
    got = exec_ir(ir2, args...)
    exp = f(args...)
    return got == exp || got === exp
end

# emit(ingest(ir)) re-structurizes (+validates) and executes identically.
function rt_restructure(f, args...)
    ir, _ = only(code_ircode(f, Tuple{map(typeof, args)...}))
    ir2 = emit(ingest(ir))
    sci = StructuredIRCode(ir2)                    # structurize + validate
    got = execute(sci, args...)
    exp = f(args...)
    return got == exp || got === exp
end

@noinline _opaque(b) = Base.compilerbarrier(:type, b)::Bool
@noinline _sink(x) = (Base.donotdelete(x); nothing)

# Representative CFG shapes spanning the corpus families. Each entry is
# (function, args-tuple); checked under both round-trip lenses.
function _corpus_cases()
    cases = Any[]
    push!(cases, (x -> x > 0 ? x + 1 : x - 1, (5,)))
    push!(cases, (x -> x > 0 ? x + 1 : x - 1, (-3,)))
    push!(cases, (x -> x > 0 ? x : -x, (7,)))
    push!(cases, ((x::Int, y::Int) -> (r = 0; if x > 0 || y > 0; r = 1; end; r), (1, -1)))
    push!(cases, ((x::Int, y::Int) -> (r = 0; if x > 0 && y > 0; r = 1; end; r), (1, 1)))
    let f = (x, y, z) -> (a = (x > 0 && y > 0) ? x * y : (z > 0 ? z + 1 : -z); a + 100)
        for args in ((1,1,1), (-1,1,1), (1,-1,1), (-1,-1,-1)); push!(cases, (f, args)); end
    end
    push!(cases, (n -> (acc = 0; for i in 1:n; acc += i; end; acc), (5,)))
    push!(cases, (n -> (i = 0; while i < n; i += 1; end; i), (5,)))
    push!(cases, (n -> (acc = 0; for i in 1:2:n; acc += i; end; acc), (7,)))
    let f = (n::Int, mq::Int) -> (s = 0; for i in 1:n, j in 1:mq; s += i*j; end; s)
        push!(cases, (f, (3, 4)))
    end
    let f = (n::Int, c::Bool) -> (cond = _opaque(c); acc = 0;
            for kt in 1:n; if cond; _sink(kt); end; if cond; acc += kt; end; end; acc)
        push!(cases, (f, (5, true))); push!(cases, (f, (5, false)))
    end
    function loop_throw(a::Vector{Float32}, n::Int)
        acc = 0.0f0
        for k in 1:n; x = @inbounds a[k]; x < 0.0f0 && throw(DomainError(x)); acc += x; end
        return acc
    end
    push!(cases, (loop_throw, (Float32[1,2,3], 3)))
    function ret_in_loop(v::Vector{Int}, n::Int)
        acc = 0; for i in 1:n; v[i] < 0 && return -i; acc += v[i]; end; return acc
    end
    push!(cases, (ret_in_loop, (Int[1,2,3], 3))); push!(cases, (ret_in_loop, (Int[1,-2,3], 3)))
    function ret_and_throw(v::Vector{Int}, n::Int)
        s = 0; for i in 1:n; v[i] == 0 && throw(DomainError(i)); v[i] < 0 && return -i; s += v[i]; end; return s
    end
    push!(cases, (ret_and_throw, (Int[1,2,3], 3)))
    function gated_loop_acc(c::Bool, v::Vector{Int}, n::Int)
        s = 0; for k in 1:n; if _opaque(c) || k > 2; s += (k == 1) ? v[k] : v[k] + 100; end; end; return s
    end
    push!(cases, (gated_loop_acc, (true, [1,2,3], 3))); push!(cases, (gated_loop_acc, (false, [5,6,7,8], 4)))
    function pi_carry(v::Vector{Any}, n::Int)
        x = 0; for i in 1:n; x = v[i]::Int; end; return x + 1
    end
    push!(cases, (pi_carry, (Any[1,2,3], 3)))
    return cases
end

@testset "multiplex (mutate-then-lift)" begin

@testset "ingest/emit round-trip identity" begin
    for (f, args) in _corpus_cases()
        @test rt_identity(f, args...)
        @test rt_restructure(f, args...)
    end
end

@testset "emit produces a well-formed CFG index" begin
    # `CFG.index` lists the first statement of blocks 2..n (length n-1), excluding
    # block 1 — an off-by-one here makes `block_for_inst` mis-map every statement.
    for (f, args) in _corpus_cases()
        ir, _ = only(code_ircode(f, Tuple{map(typeof, args)...}))
        ir2 = emit(ingest(ir))
        @test length(ir2.cfg.index) == length(ir2.cfg.blocks) - 1
        @test ir2.cfg.index == [first(b.stmts) for b in ir2.cfg.blocks[2:end]]
    end
end

# Structurize a muxed IRCode and execute it (build_ir comes from corpus.jl).
mux_exec(m, args...) = exec_ir(CCx.IRCode(StructuredIRCode(emit(m))), args...)

@testset "EdgeMultiplexer" begin
    @testset "2-entry continuation (short-circuit shape)" begin
        # `(a || b) ? 99 : 0`. The continuation {body, merge} is reached from both
        # arms — exactly the multi-entry case the mux collapses to single-entry.
        sc_ir() = build_ir([
            (stmts=[(GotoIfNot(Argument(2), 3), Any)], succs=[3, 2]),   # E:  a false→chk, true→body-jmp
            (stmts=[(GotoNode(4), Any)],               succs=[4]),       # →body
            (stmts=[(GotoIfNot(Argument(3), 5), Any)], succs=[5, 4]),    # chk: b false→merge, true→body
            (stmts=[(GotoNode(5), Any)],               succs=[5]),       # body→merge
            (stmts=[(PhiNode(Int32[4, 3], Any[99, 0]), Int),
                    (ReturnNode(SSAValue(5)), Any)],   succs=Int[]),     # merge: φ(body=>99, chk=>0)
        ], Any[Any, Bool, Bool])
        cases = ((false, false), (false, true), (true, false), (true, true))
        # baseline: the un-muxed CFG already structurizes to (a||b) ? 99 : 0
        let sci = StructuredIRCode(sc_ir())
            @test [exec_ir(CCx.IRCode(sci), a, b) for (a, b) in cases] == [0, 99, 99, 99]
        end

        m = ingest(sc_ir())
        mux = single_entry_mux!(m, [EdgeRef(2, :goto), EdgeRef(3, :t), EdgeRef(3, :f)])
        @test mux.entries == [4, 5]            # body, merge — the two distinct entries
        @test mux.disc_id != 0                 # >1 entry → a discriminator
        # every redirected edge now lands on the single mux block (single-entry)
        @test all(r -> edge_of(m, r).target == mux.mux_id,
                  [EdgeRef(2, :goto), EdgeRef(3, :t), EdgeRef(3, :f)])
        @test [mux_exec(m, a, b) for (a, b) in cases] == [0, 99, 99, 99]
    end

    @testset "N-entry dispatch (compare-chain)" begin
        # Three distinct entries → a 2-deep compare-chain. `p ? (q ? 10 : 30) : 20`.
        ir3() = build_ir([
            (stmts=[(GotoIfNot(Argument(2), 4), Any)], succs=[4, 2]),
            (stmts=[(GotoIfNot(Argument(3), 5), Any)], succs=[5, 3]),
            (stmts=[(GotoNode(6), Any)],               succs=[6]),   # → A
            (stmts=[(GotoNode(7), Any)],               succs=[7]),   # → B
            (stmts=[(GotoNode(8), Any)],               succs=[8]),   # → C
            (stmts=[(ReturnNode(10), Any)],            succs=Int[]),
            (stmts=[(ReturnNode(20), Any)],            succs=Int[]),
            (stmts=[(ReturnNode(30), Any)],            succs=Int[]),
        ], Any[Any, Bool, Bool])
        cases = ((true, true), (true, false), (false, true), (false, false))

        m = ingest(ir3())
        mux = single_entry_mux!(m, [EdgeRef(3, :goto), EdgeRef(4, :goto), EdgeRef(5, :goto)])
        @test mux.entries == [6, 7, 8]
        @test [mux_exec(m, p, q) for (p, q) in cases] == [10, 30, 20, 20]
    end
end

end  # multiplex
