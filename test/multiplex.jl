#=============================================================================
 Mutate-then-lift CFG normalization (src/structurize/multiplex.jl).

 M1 foundation: the explicit-edge mutable form (`ingest`/`emit`) must rebuild an
 IRCode that is faithful enough to (a) execute identically and (b) re-structurize
 identically — `emit(ingest(ir))` is the no-mutation identity that M2/M3 build on.
 The EdgeMultiplexer unit tests then check the mux primitive on synthetic
 multi-entry CFGs.
=============================================================================#

const CCx = Core.Compiler
using IRStructurizer: ingest, emit, MCFG, MBlock, MEdge, MGoto, MCondBr, MReturn

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

end  # multiplex
