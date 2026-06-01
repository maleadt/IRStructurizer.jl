#=============================================================================
 Golden corpus — the standing regression net for the CFGToSCF alignment.

 One @testset per CFG family (tagged by the GROUND_TRUTH.md watch-list row it
 exercises), plus the RESEARCH_ANSWER.md divergence CFGs (Q1/Q2/Q3) built as
 synthetic IR with structural assertions, and a renumbering-invariance check
 (invariant I1). Every entry is an executable @roundtrip (invariant I7) unless
 it is a pure structural assertion.

 The synthetic-IR builder lets us pin the exact CFG shapes from the research
 (which natural Julia source can't reliably produce) and assert directly on the
 structure (merge = M, body emitted once), not only through the I7 keyhole.
=============================================================================#

const CC = Core.Compiler
using Core: Argument

# Build an IRCode from explicit blocks. Each block is `(stmts, succs)`:
#   stmts :: Vector of (stmt, type)  — SSA indices are assigned in this order
#   succs :: Vector{Int}             — successor block indices (1-based)
# Predecessors are derived from succs. `argtypes[1]` is the closure-self type.
function build_ir(blocks::Vector, argtypes::Vector)
    nstmts = sum(length(b.stmts) for b in blocks)
    stmts = CC.InstructionStream(nstmts)
    ranges = UnitRange{Int}[]
    pos = 0
    for b in blocks
        start = pos + 1
        for (s, t) in b.stmts
            pos += 1
            inst = stmts[pos]
            inst[:stmt] = s
            inst[:type] = t
            inst[:info] = CC.NoCallInfo()
            inst[:line] = (Int32(0), Int32(0), Int32(0))
            inst[:flag] = CC.IR_FLAGS_EFFECTS
        end
        push!(ranges, start:pos)
    end
    nb = length(blocks)
    preds = [Int[] for _ in 1:nb]
    for (i, b) in enumerate(blocks), s in b.succs
        push!(preds[s], i)
    end
    bbs = [CC.BasicBlock(CC.StmtRange(first(ranges[i]), last(ranges[i])),
                         preds[i], copy(blocks[i].succs)) for i in 1:nb]
    cfg = CC.CFG(bbs, Int[first(r) for r in ranges])
    debuginfo = CC.DebugInfoStream(Int32[0 for _ in 1:nstmts])
    return CC.IRCode(stmts, cfg, debuginfo, argtypes, Expr[], CC.VarState[])
end

# Total emitted occurrences of each statement matching `pred`, recursively
# across all nested control-flow blocks (invariant I2: no duplication).
function count_stmts(blk::Block, pred)
    n = 0
    for (_, entry) in blk.body
        pred(entry.stmt) && (n += 1)
        if entry.stmt isa ControlFlowOp
            for sub in IRStructurizer.blocks(entry.stmt)
                n += count_stmts(sub, pred)
            end
        end
    end
    return n
end

iscall_to(stmt, fname::Symbol) =
    stmt isa Expr && stmt.head === :call && !isempty(stmt.args) &&
    (c = stmt.args[1]; c isa GlobalRef && c.name === fname)

@testset "golden corpus" begin

#=============================================================================
 Divergence CFGs (RESEARCH_ANSWER.md Q1/Q2/Q3) — structural assertions
=============================================================================#

@testset "Q1: successor that is also a merge (D-split)" begin
    # E→{T,F}, F→T, T→X.  T has two predecessors (E and F), so by edge-domination
    # T's branch region is EMPTY and T is the continuation — not pulled into the
    # then-region (which block-domination would do). A φ at T gives cond ? 10 : 20.
    function q1_ir()
        build_ir([
            (stmts=[(GotoIfNot(Argument(2), 3), Any)], succs=[3, 2]),     # E: false→F, true→T
            (stmts=[(PhiNode(Int32[1, 3], Any[10, 20]), Int),             # T: φ(E=>10, F=>20)
                    (GotoNode(4), Any)],               succs=[4]),         # T→X
            (stmts=[(GotoNode(2), Any)],               succs=[2]),         # F→T
            (stmts=[(ReturnNode(SSAValue(2)), Any)],   succs=Int[]),       # X: return φ
        ], Any[Any, Bool])
    end

    ir = q1_ir()
    ctx = IRStructurizer.StructurizeCtx(ir)
    region = Set(1:length(ir.cfg.blocks))
    then_blocks, else_blocks, merge =
        IRStructurizer.find_branch_regions(ctx, 1, 2, 3, region)  # E: true=BB2, false=BB3
    @test merge == 2                       # T is the continuation
    @test !(2 in then_blocks)              # ...not swallowed into an arm
    @test !(2 in else_blocks)
    @test isempty(then_blocks)             # T's branch region is empty (2 preds)

    sci = StructuredIRCode(q1_ir())
    @test execute(sci, true) == 10
    @test execute(sci, false) == 20
end

@testset "Q2: virtual exit, continuation by exclusion (D-merge, I1)" begin
    # E→{T,F}, T→M, F→{M,R}, R:return, M→X.  ipdom(E) is the virtual exit (F
    # reaches R without M), yet the continuation is unambiguously M. A φ at M
    # gives cond ? 100 : (c2 ? 200 : 999). Built in two block layouts to assert
    # the merge is M regardless of numbering (I1: layout independence).
    function q2_ir(; m_first::Bool)
        if !m_first
            blocks = [  # BB1=E BB2=T BB3=F BB4=M BB5=R BB6=X
                (stmts=[(GotoIfNot(Argument(2), 3), Any)], succs=[3, 2]),
                (stmts=[(GotoNode(4), Any)],               succs=[4]),
                (stmts=[(GotoIfNot(Argument(3), 5), Any)], succs=[5, 4]),
                (stmts=[(PhiNode(Int32[2, 3], Any[100, 200]), Int),
                        (GotoNode(6), Any)],               succs=[6]),
                (stmts=[(ReturnNode(999), Any)],           succs=Int[]),
                (stmts=[(ReturnNode(SSAValue(4)), Any)],   succs=Int[]),
            ]
            return build_ir(blocks, Any[Any, Bool, Bool]), 4   # M is BB4
        else
            blocks = [  # BB1=E BB2=T BB3=M BB4=X BB5=F BB6=R
                (stmts=[(GotoIfNot(Argument(2), 5), Any)], succs=[5, 2]),
                (stmts=[(GotoNode(3), Any)],               succs=[3]),
                (stmts=[(PhiNode(Int32[2, 5], Any[100, 200]), Int),
                        (GotoNode(4), Any)],               succs=[4]),
                (stmts=[(ReturnNode(SSAValue(3)), Any)],   succs=Int[]),
                (stmts=[(GotoIfNot(Argument(3), 6), Any)], succs=[6, 3]),
                (stmts=[(ReturnNode(999), Any)],           succs=Int[]),
            ]
            return build_ir(blocks, Any[Any, Bool, Bool]), 3   # M is BB3
        end
    end

    for m_first in (false, true)
        ir, m_bb = q2_ir(; m_first)
        ctx = IRStructurizer.StructurizeCtx(ir)
        region = Set(1:length(ir.cfg.blocks))
        fdest = (ir.stmts.stmt[ir.cfg.blocks[1].stmts[end]]::GotoIfNot).dest
        _, _, merge = IRStructurizer.find_branch_regions(ctx, 1, 2, fdest, region)
        @test merge == m_bb                # M chosen regardless of its index

        sci = StructuredIRCode(q2_ir(; m_first)[1])
        @test execute(sci, true,  true)  == 100   # cond
        @test execute(sci, false, true)  == 200   # !cond, c2
        @test execute(sci, false, false) == 999   # !cond, !c2 → R
    end
end

@testset "Q3: short-circuit || body emitted once (D-dup, I2)" begin
    # `if a || b { body }` — body is the multi-entry continuation reached from
    # both arms. The edge multiplexer emits it exactly once (no tail duplication).
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    function or_body!(r::Base.RefValue{Int}, a::Bool, b::Bool)
        if opaque(a) || opaque(b)
            r[] = 99
        end
        return nothing
    end
    sci, _ = code_structured(or_body!, Tuple{Base.RefValue{Int}, Bool, Bool}) |> only
    @test count_stmts(sci.entry, s -> iscall_to(s, :setfield!)) == 1   # once, not twice
    for (a, b) in ((false, false), (false, true), (true, false), (true, true))
        r = Ref(0); execute(sci, r, a, b)
        @test r[] == ((a || b) ? 99 : 0)
    end
end

#=============================================================================
 Watch-list families — executable @roundtrip net (I7)
=============================================================================#

@testset "baseline: diamond / ternary" begin
    @test @roundtrip (x -> x > 0 ? x + 1 : x - 1)(5)
    @test @roundtrip (x -> x > 0 ? x + 1 : x - 1)(-3)
    @test @roundtrip (x -> x > 0 ? x : -x)(7)
end

@testset "D-dup: short-circuit && / || and shared tail" begin
    f_or  = (x::Int, y::Int) -> (r = 0; if x > 0 || y > 0; r = 1; end; r)
    f_and = (x::Int, y::Int) -> (r = 0; if x > 0 && y > 0; r = 1; end; r)
    for (x, y) in ((1, -1), (-1, 1), (-1, -1), (1, 1))
        @test @roundtrip f_or(x, y)
        @test @roundtrip f_and(x, y)
    end
    # nested short-circuit with a shared value-producing tail
    f_nest = (x, y, z) -> (a = (x > 0 && y > 0) ? x * y : (z > 0 ? z + 1 : -z); a + 100)
    for args in ((1,1,1), (-1,1,1), (1,-1,1), (-1,-1,-1), (1,-1,-1))
        @test @roundtrip f_nest(args...)
    end
end

@testset "D-dup: gated body with in-body region-exits and a loop-carried value" begin
    # Regression (silent miscompile): a `||`-guarded body inside a loop whose body
    # both (a) contains bounds-check throws — region-exits that dead-end OUT of the
    # loop, so they aren't in loop_blocks — and (b) produces a value folded into a
    # loop-carried accumulator. find_gated_body's closure check rejected the
    # out-of-loop throw successors, so the multiplexer bailed and the diverge path
    # silently dropped the whole body (the accumulator stayed 0). The closure check
    # now treats any no-successor block as a region-exit kept in the body.
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    function gated_loop_acc(c::Bool, v::Vector{Int}, n::Int)
        s = 0
        for k in 1:n
            if opaque(c) || k > 2
                s += (k == 1) ? v[k] : v[k] + 100
            end
        end
        return s
    end
    sci, _ = code_structured(gated_loop_acc, Tuple{Bool, Vector{Int}, Int}) |> only
    @test count_stmts(sci.entry, s -> iscall_to(s, :memoryrefget)) >= 1  # body present, not dropped
    for (c, v, n) in ((false, [1,2,3], 3), (true, [1,2,3], 3),
                      (false, [5,6,7,8], 4), (true, [1], 0))
        @test execute(sci, c, v, n) == gated_loop_acc(c, v, n)
    end

    # A `||`-guarded body that itself early-returns (body has an internal
    # region-exit reaching past the guard's continuation).
    f_ret = (a::Bool, b::Bool, x::Int) -> (if opaque(a) || opaque(b); x > 0 && return x; end; -1)
    sci_r, _ = code_structured(f_ret, Tuple{Bool, Bool, Int}) |> only
    for (a, b, x) in ((true, false, 5), (true, false, -5), (false, false, 5))
        @test execute(sci_r, a, b, x) == f_ret(a, b, x)
    end

    # Two sequential ||-guards threading a value through the shared merge.
    function f_seq(a::Bool, b::Bool, n::Int)
        if opaque(a) || opaque(b); t = n + 1; else; t = n - 1; end
        if opaque(a) || opaque(b); return t * 2; end
        return t
    end
    sci_s, _ = code_structured(f_seq, Tuple{Bool, Bool, Int}) |> only
    for a in (false, true), b in (false, true)
        @test execute(sci_s, a, b, 3) == f_seq(a, b, 3)
    end
end

@testset "D-absorb: sequential ifs sharing a condition in a loop" begin
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    @noinline sink(x) = (Base.donotdelete(x); nothing)
    function seq_ifs_loop(n::Int, c::Bool)
        cond = opaque(c); acc = 0
        for kt in 1:n
            if cond; sink(kt); end
            if cond; acc += kt; end
        end
        return acc
    end
    @test @roundtrip seq_ifs_loop(5, true)
    @test @roundtrip seq_ifs_loop(5, false)
    @test @roundtrip seq_ifs_loop(0, true)
end

@testset "D-merge: early return inside a branch (virtual exit)" begin
    f_early = (x::Int, y::Int) -> (x > y ? (return y * x) : nothing; y - x)
    @test @roundtrip f_early(5, 3)
    @test @roundtrip f_early(3, 5)
end

@testset "D-throw / I8: throw inside a loop and inside a branch" begin
    function loop_throw(a::Vector{Float32}, n::Int)
        acc = 0.0f0
        for k in 1:n
            x = @inbounds a[k]
            x < 0.0f0 && throw(DomainError(x))
            acc += x
        end
        return acc
    end
    sci, _ = code_structured(loop_throw, Tuple{Vector{Float32}, Int}) |> only
    @test execute(sci, Float32[1, 2, 3], 3) == 6.0f0
    @test_throws DomainError execute(sci, Float32[1, -2, 3], 3)

    branch_throw = (x::Int) -> (x < 0 ? throw(DomainError(x)) : x + 1)
    sci2, _ = code_structured(branch_throw, Tuple{Int}) |> only
    @test execute(sci2, 4) == 5
    @test_throws DomainError execute(sci2, -1)
end

@testset "I8: early return inside a loop (region-exit re-materialization)" begin
    # A `return` block inside a loop is a region-exit (no successors), like a
    # throw. Collapsing it to a bare BreakOp dropped the returned value (it failed
    # to structurize at all — "SSA used but not defined"). It must be
    # re-materialized in place, while the loop's *primary* exit still breaks.
    function ret_in_loop(v::Vector{Int}, n::Int)
        acc = 0
        for i in 1:n
            v[i] < 0 && return -i
            acc += v[i]
        end
        return acc
    end
    sci, _ = code_structured(ret_in_loop, Tuple{Vector{Int}, Int}) |> only
    for (v, n) in ((Int[1,2,3], 3), (Int[1,-2,3], 3), (Int[-1,2], 2), (Int[1,2], 0))
        @test execute(sci, v, n) == ret_in_loop(v, n)
    end

    function ret_while(n::Int)
        i = 0
        while i < n
            i += 1
            i == 3 && return 100
        end
        return i
    end
    sci2, _ = code_structured(ret_while, Tuple{Int}) |> only
    for n in (1, 5, 2, 0)
        @test execute(sci2, n) == ret_while(n)
    end

    # return AND throw both inside the same loop — two distinct secondary exits.
    function ret_and_throw(v::Vector{Int}, n::Int)
        s = 0
        for i in 1:n
            v[i] == 0 && throw(DomainError(i))
            v[i] < 0 && return -i
            s += v[i]
        end
        return s
    end
    sci3, _ = code_structured(ret_and_throw, Tuple{Vector{Int}, Int}) |> only
    @test execute(sci3, Int[1, 2, 3], 3) == 6
    @test execute(sci3, Int[1, -2, 3], 3) == -2
    @test_throws DomainError execute(sci3, Int[1, 0, 3], 3)
end

@testset "I6 / promote: counted for, step range, while" begin
    @test @roundtrip ((n::Int) -> (acc = 0; for i in 1:n; acc += i; end; acc))(5)
    @test @roundtrip ((n::Int) -> (i = 0; while i < n; i += 1; end; i))(5)
    @test @roundtrip ((n::Int) -> (acc = 0; for i in 1:2:n; acc += i; end; acc))(7)
    @test @roundtrip ((n::Int) -> (i = 0; while i <= n; i += 1; end; i))(4)
end

@testset "I6: the core walk emits only LoopOp (promotion is a post-pass)" begin
    # With `promote=false`, every loop must be a generic LoopOp — no ForOp/WhileOp
    # leaks from the core walk. (With promotion they become For/While; that path is
    # exercised above.) Counted, step-range, and condition loops all qualify.
    function no_forwhile(blk::Block)
        for (_, e) in blk.body
            (e.stmt isa ForOp || e.stmt isa WhileOp) && return false
            if e.stmt isa ControlFlowOp
                for b in IRStructurizer.blocks(e.stmt)
                    no_forwhile(b) || return false
                end
            end
        end
        return true
    end
    for f in (n -> (acc = 0; for i in 1:n; acc += i; end; acc),
              n -> (i = 0; while i < n; i += 1; end; i),
              n -> (acc = 0; for i in 1:2:n; acc += i; end; acc))
        ir, _ = only(code_ircode(f, Tuple{Int}))
        sci_raw = StructuredIRCode(ir; promote=false)
        @test no_forwhile(sci_raw.entry)
        # ...and with promotion the same IR yields a counted ForOp somewhere.
        sci_pro = StructuredIRCode(ir; promote=true)
        @test !no_forwhile(sci_pro.entry)
    end
end

@testset "I5: PiNode carry and :invoke closure" begin
    # A value used through a PiNode after the loop must be threaded out.
    function pi_carry(v::Vector{Any}, n::Int)
        x = 0
        for i in 1:n
            x = v[i]::Int
        end
        return x + 1
    end
    @test @roundtrip pi_carry(Any[1, 2, 3], 3)

    # A closure applied via :invoke counts its callee operand as a use.
    function invoke_closure(n::Int)
        acc = 0
        f = y -> y + 1
        for i in 1:n
            acc += f(i)
        end
        return acc
    end
    @test @roundtrip invoke_closure(4)
end

@testset "D-mux: irreducible CFGs (entry multiplexer)" begin
    # `@goto` produces multi-entry SCCs that no block dominates — irreducible.
    # normalize_cf inserts one entry multiplexer (the disc-as-carried-value form):
    # the SCC's entry blocks collapse to a single loop header that dispatches on a
    # discriminator carry, and a latch unifies the back edges. The result is a
    # plain reducible LoopOp the existing lift handles. (Was rejected with
    # UnstructuredControlFlowError; see GROUND_TRUTH.md §3 D-mux.)

    # Canonical 2-entry SCC {BB3,BB5,BB6,BB8}, entries BB3 (from BB1) and BB6
    # (from BB2). Only terminating inputs (x<=0 with small y oscillates forever,
    # in the source too).
    function irreducible(x::Int, y::Int)
        if x > 0; @goto L2; end
        @label L1; y += x; if y > 100; return y; end; @goto L2_body
        @label L2; @label L2_body; y += 1; if y > 100; return y; end; @goto L1
    end
    for (x, y) in ((1, 50), (5, 200), (3, 98), (2, -10), (0, 0), (-1, 200), (100, 1))
        @test @roundtrip irreducible(x, y)
    end

    # 3-entry SCC → an N=3 discriminator compare-chain in the mux dispatch.
    function irr3(s::Int, n::Int)
        acc = 0
        s == 0 && @goto A
        s == 1 && @goto B
        @goto C
        @label A; acc += 1; acc > n && return acc; @goto B
        @label B; acc += 2; acc > n && return acc; @goto C
        @label C; acc += 3; acc > n && return acc; @goto A
    end
    for (s, n) in ((0, 10), (1, 10), (2, 10), (0, 0), (1, 5), (2, 100))
        @test @roundtrip irr3(s, n)
    end

    # Structural: the SCC collapses to exactly one LoopOp (irreducible loops stay
    # LoopOp — no While/For promotion, there is no single counting condition), and
    # structurization succeeds + validates (no UnstructuredControlFlowError).
    sci, _ = code_structured(irreducible, Tuple{Int, Int}) |> only
    @test count_stmts(sci.entry, s -> s isa LoopOp) == 1
    sci3, _ = code_structured(irr3, Tuple{Int, Int}) |> only
    @test count_stmts(sci3.entry, s -> s isa LoopOp) == 1

    # Determinism (I1): structurizing the same IR twice yields the same shape —
    # the mux sorts its entries, so no iteration-order nondeterminism leaks in.
    ir, _ = only(code_ircode(irr3, Tuple{Int, Int}))
    s1 = sprint(show, MIME"text/plain"(), StructuredIRCode(ir))
    s2 = sprint(show, MIME"text/plain"(), StructuredIRCode(ir))
    @test s1 == s2
end

@testset "I4: nested gated bodies (continuation multiplexer)" begin
    # The canonical case the continuation multiplexer fixes. A `||`-guarded body
    # whose body is ITSELF a `||`-guarded body, inside a loop carrying an
    # accumulator. On the #48 baseline this silently miscompiled; on the rework
    # baseline (2-entry `find_gated_body`) it failed loudly via SSA validation.
    # Now every multi-pred continuation is collapsed to single-entry upstream, so
    # the ordinary IfOp lift handles arbitrary nesting (invariant I4).
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool
    function nested_gated(a::Bool, b::Bool, n::Int)
        s = 0
        for k in 1:n
            if opaque(a) || k > 1
                if opaque(b) || k > 2
                    s += k
                end
            end
        end
        return s
    end
    sci, _ = code_structured(nested_gated, Tuple{Bool, Bool, Int}) |> only  # must not throw
    # The innermost guarded write `s += k` (a memoryref-free add into the carry)
    # is emitted once, not duplicated per guard arm (invariant I2).
    @test count_stmts(sci.entry, s -> iscall_to(s, :add_int)) == 2   # `s += k` and the IV `k += 1`
    for a in (false, true), b in (false, true), n in (0, 1, 3, 5)
        @test execute(sci, a, b, n) == nested_gated(a, b, n)
    end

    # Three-deep nesting, value-producing (each level contributes to the result).
    function nest3(a::Bool, b::Bool, c::Bool, x::Int)
        r = 0
        if opaque(a) || x > 0
            if opaque(b) || x > 1
                if opaque(c) || x > 2
                    r = x * 10
                end
            end
        end
        return r
    end
    sci3, _ = code_structured(nest3, Tuple{Bool, Bool, Bool, Int}) |> only
    for a in (false, true), b in (false, true), c in (false, true), x in (-1, 0, 1, 2, 3)
        @test execute(sci3, a, b, c, x) == nest3(a, b, c, x)
    end
end

@testset "fuzz: multi-entry shapes, exec vs direct" begin
    # The corpus families' two latent silent miscompiles were both found by
    # fuzzing with exec-vs-direct, not by a green structural net. Enumerate
    # short-circuit / nested-guard / guard-in-loop / guard-with-early-exit shapes
    # and assert structurize→unstructurize→execute == direct for every input.
    @noinline opaque(b) = Base.compilerbarrier(:type, b)::Bool

    fns = Any[
        # mixed &&/|| chains
        (x::Int, y::Int, z::Int) -> ((opaque(x > 0) || y > 0) && z > 0) ? 1 : 2,
        (x::Int, y::Int, z::Int) -> (opaque(x > 0) && (y > 0 || z > 0)) ? 1 : 2,
        (x::Int, y::Int, z::Int) -> (x > 0 || y > 0 || z > 0) ? 1 : 2,
        (x::Int, y::Int, z::Int) -> (x > 0 && y > 0 && z > 0) ? 1 : 2,
        # guard in a loop feeding a carried accumulator
        (a::Bool, n::Int) -> (s = 0; for k in 1:n; if opaque(a) || k > 2; s += k; end; end; s),
        # nested guards in a loop
        (a::Bool, b::Bool, n::Int) -> (s = 0; for k in 1:n
            if opaque(a) || k > 1; if opaque(b) || k > 2; s += k * k; end; end; end; s),
        # guard whose body early-returns
        (a::Bool, b::Bool, x::Int) -> (if opaque(a) || opaque(b); x > 0 && return x; end; -1),
        # value defined in one guard, used in a later guard (undef phi slot)
        (c1::Bool, c2::Bool, n::Int) -> (local t; if c1 || c2; t = n + 1; end;
                                         s = 0; if c1 || c2; s = t; end; s),
        # sequential guards threading a value through the shared merge
        (a::Bool, b::Bool, n::Int) -> (if opaque(a) || opaque(b); t = n + 1; else; t = n - 1; end;
                                       if opaque(a) || opaque(b); return t * 2; end; t),
    ]
    args_for(nparams) = nparams == 2 ? [(false, 5), (true, 5), (false, 0), (true, 3)] :
        nparams == 3 ? Iterators.product((false, true), (false, true), (-1, 0, 1, 2)) |> collect |> vec :
        []
    nfuzz = 0
    for f in fns
        m = only(methods(f))
        nparams = m.nargs - 1
        # Build the type signature and the input set from parameter kinds.
        ms = code_structured(f) |> only
        sci = ms.first
        # Infer inputs: enumerate booleans for Bool params, small ints otherwise.
        ptypes = [fieldtype(Base.tuple_type_tail(m.sig), i) for i in 1:nparams]
        choices = [pt === Bool ? (false, true) : (-1, 0, 1, 2, 5) for pt in ptypes]
        for combo in Iterators.product(choices...)
            exp = f(combo...)
            got = execute(sci, combo...)
            @test got == exp
            nfuzz += 1
        end
    end
    @test nfuzz > 100   # sanity: the fuzz actually ran a meaningful number of cases
end

end  # golden corpus
