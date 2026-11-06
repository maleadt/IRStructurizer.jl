#=============================================================================
 Mutate-then-lift CFG normalization (src/structurize/multiplex.jl).

 The structurizer works on the explicit-edge `MCFG` (`ingest` from IRCode, lift to
 SCI via `lift_mcfg`) — there is no dense round-trip. These tests exercise the
 `EdgeMultiplexer` primitive directly on synthetic multi-entry CFGs: mux the
 distinct targets, then lift + execute and check the result. End-to-end mux
 coverage (short-circuits, irreducible headers, multi-exit loops) lives in the
 regression suite and the loop fuzzer.
=============================================================================#

const CCx = Core.Compiler
using IRStructurizer: ingest, lift_mcfg, MCFG, MBlock, MEdge, MGoto, MCondBr, MReturn,
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

# Lift a (manually muxed) MCFG to an SCI and execute it (build_ir comes from setup.jl).
mux_exec(m, args...) = exec_ir(CCx.IRCode(lift_mcfg(m)), args...)

# Shapes that need several normalization rounds: short-circuit continuations, a loop
# with several exits, values defined in a loop and used after it.
function norm_gates(n::Int, k::Int)
    s = 0
    for i in 1:n
        if (i % 2 == 0 || i < k) && (i % 3 != 0 || k < 0)
            s += i
        elseif i == k
            s -= 2
        end
    end
    return s
end
function norm_exits(n::Int, k::Int)
    s = 0; i = 0
    while i < n
        i += 1
        i == k && continue
        i > 2k && k > 0 && break
        for j in 1:k
            j == i && continue
            j + i > 20 && return s
            s += i - j
        end
    end
    return s
end
function norm_escapes(n::Int, k::Int)
    a = 0; b = 1; c = 0
    i = 0
    while i < n
        i += 1
        a = i * k
        b = b + a
        i == k && break
        c = a - b
        b > 1000 && break
        a < -50 && return a + c
    end
    return a + 2b + 3c
end

# `normalize_cf!` without shared analyses: every pass computes its own CFG, dominator
# tree and loops, and the continuation scan starts at the first block every round.
function normalize_unshared!(m)
    guard = 0
    limit = 8 * (length(m.blocks) + 16)      # as normalize_cf!: from the blocks before muxing
    while IRStructurizer.normalize_one_irreducible!(m) || IRStructurizer.normalize_one_loop_latch!(m) ||
          IRStructurizer.normalize_one_continuation!(m) || IRStructurizer.normalize_one_preheader!(m)
        (guard += 1) > limit && error("did not converge")
    end
    return IRStructurizer.drop_undef_args!(m)
end

@testset "multiplex (mutate-then-lift)" begin

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

@testset "normalize_cf! with shared analyses and a resumed scan" begin
    # The same normalized CFG as with every pass computing its own analyses and
    # scanning from the entry, and code that runs the same.
    for f in (norm_gates, norm_exits, norm_escapes)
        ir = first(only(code_ircode(f, Tuple{Int, Int})))
        reference = normalize_unshared!(ingest(ir))
        m = ingest(ir)
        IRStructurizer.normalize_cf!(m)
        @test repr(m) == repr(reference)
        sci = lift_mcfg(m; promote=false)
        for n in (0, 1, 7, 20, 100), k in (-1, 0, 2, 6, 10, 20)
            @test exec_ir(CCx.IRCode(sci), n, k) == f(n, k)
        end
    end
end

@testset "mux arguments that no edge defines" begin
    # A mux's arguments for one entry's values are `Undef` on the edges into the
    # others; where no edge defines one and nothing reads it, it is no IfOp result.
    sci, _ = only(code_structured(norm_exits, Tuple{Int, Int}))
    undefined = 0
    walk(sci) do inst, _
        op = inst[:stmt]
        op isa IfOp && inst[:type] <: Tuple || return
        arms = (op.then_region.terminator, op.else_region.terminator)
        for i in 1:fieldcount(inst[:type])
            all(t -> !(t isa YieldOp) || t.values[i] isa IRStructurizer.Undef, arms) &&
                (undefined += 1)
        end
    end
    @test undefined == 0
end

end  # multiplex
