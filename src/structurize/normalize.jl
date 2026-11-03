#=============================================================================
 normalize_cf: the mutate-then-lift driver.

 Repeatedly find one multi-entry situation and collapse it to single-entry with an
 EdgeMultiplexer, until none remain. The lift (`structurize_region!`) then only
 ever sees single-entry regions.
=============================================================================#

_term_targets(t::MGoto) = (t.edge.target,)
_term_targets(t::MCondBr) = (t.t.target, t.f.target)
_term_targets(t::MReturn) = ()
# Both edges of an enter are CFG edges (dominance, loops, reachability see the
# handler), but neither is ever redirected: `_edge_refs_of`/`edge_refs` expose none.
_term_targets(t::MEnter) = t.catch_dest == 0 ? (t.body.target,) : (t.body.target, t.catch_dest)

"""A lightweight `CFG` over the mutable blocks (preds/succs only; statement
ranges are placeholders) for dominance / SCC queries during normalization. Block
indices equal MBlock ids, so results map straight back.

Unlike Julia's own CFG, preds/succs keep one entry per edge: a conditional branch
with both edges to one block lists it twice, so that block is not a
single-predecessor arm in `find_branch_regions`. Code collecting edges must
therefore not pair this adjacency with `edge_refs`, which already returns every
edge between two blocks."""
function build_cfg(m::MCFG)
    nb = length(m.blocks)
    succs = [Int[] for _ in 1:nb]
    preds = [Int[] for _ in 1:nb]
    for (i, b) in enumerate(m.blocks)
        for tgt in _term_targets(b.term)
            push!(succs[i], tgt)
            push!(preds[tgt], i)
        end
    end
    bbs = [BasicBlock(StmtRange(i, i), preds[i], succs[i]) for i in 1:nb]
    return CFG(bbs, collect(1:nb))
end

"""Find one irreducible (multi-entry) SCC and collapse its entry blocks to a
single entry with a mux (MLIR's `createSingleEntryBlock` over entry and back
edges). Returns `true` if it muxed one, `false` if the CFG has no irreducible
SCC."""
function normalize_one_irreducible!(m::MCFG, cfg::CFG=build_cfg(m),
                                    domtree::DomTree=construct_domtree(cfg))
    reach = CFGReachability(cfg, domtree)
    nb = length(m.blocks)

    by_scc = Dict{Int, Vector{Int}}()
    for bb in 1:nb
        # `irreducible` is only initialized for reachable blocks
        @assert !CC.bb_unreachable(reach, bb) "unreachable block $bb in the MCFG"
        CC.bb_in_irreducible_loop(reach, bb) && push!(get!(Vector{Int}, by_scc, reach.scc[bb]), bb)
    end
    isempty(by_scc) && return false

    # Deterministic pick: smallest SCC id, entry blocks sorted.
    S = by_scc[minimum(keys(by_scc))]
    Sset = Set(S)
    entry_blocks = sort!([b for b in S if any(p -> p ∉ Sset, cfg.blocks[b].preds)])
    @assert length(entry_blocks) >= 1 "irreducible SCC with no entry block"

    # Separate the edges into entry blocks: external (entry edges) and in-SCC
    # (back edges). Both route through the entry mux so every in-edge, back edges
    # included, lands on the single header (MLIR's `createSingleEntryBlock` passing
    # both entryEdges and backEdges).
    entry_refs = EdgeRef[]
    back_refs = EdgeRef[]
    for src in sort!(collect(1:nb)), e in entry_blocks
        dst = src in Sset ? back_refs : entry_refs
        append!(dst, edge_refs(m, src, e))
    end

    # Entry mux: collapse the multiple entry blocks to one header. It absorbs the
    # entries' args (becoming the loop header that carries them); each entry is a
    # dispatch arm reached only from the mux and reads them directly. The header now
    # has several back-edge predecessors; unifying those into one back edge is the
    # single-exiting latch's job, fired next by `normalize_one_loop_latch!` on the
    # >=2-back-edge trigger, so there is no separate back-edge mux here.
    single_entry_mux!(m, vcat(entry_refs, back_refs); absorb=true)
    return true
end

# single-exiting latch ---------------------------------------------------------

"""Natural loops on the MBlock CFG: header id to set of in-loop block ids. A back
edge is `src->header` where `header` dominates `src`."""
function natural_loops_m(m::MCFG, cfg::CFG=build_cfg(m),
                         domtree::DomTree=construct_domtree(cfg))
    loops = Dict{Int, Set{Int}}()
    nb = length(m.blocks)
    for src in 1:nb
        for h in _term_targets(m.blocks[src].term)
            dominates(domtree, h, src) || continue
            body = get!(Set{Int}, loops, h)
            push!(body, h)
            wl = Int[src]
            while !isempty(wl)
                b = pop!(wl)
                b in body && continue
                push!(body, b)
                append!(wl, cfg.blocks[b].preds)
            end
        end
    end
    return loops
end

_edge_refs_of(src::Int, t::MGoto)   = (EdgeRef(src, :goto),)
_edge_refs_of(src::Int, t::MCondBr) = (EdgeRef(src, :t), EdgeRef(src, :f))
_edge_refs_of(src::Int, t::MReturn) = ()
_edge_refs_of(src::Int, t::MEnter)  = ()

"""Route a loop's back edges and exit edges through one latch (MLIR's
`createSingleExitingLatch`). Back edges carry `shouldRepeat=1`, exit edges `=0`;
the latch branches on `shouldRepeat` back to `header` (the single back edge) or to
a fresh exit-dispatch block that switches to the original exit targets (the single
exit edge). The loop is then single-back-edge and single-exit-edge."""
function single_exiting_latch!(m::MCFG, header::Int,
                               back_refs::Vector{EdgeRef}, exit_refs::Vector{EdgeRef})
    exit_targets = Int[]
    for r in exit_refs
        t = edge_of(m, r).target
        t in exit_targets || push!(exit_targets, t)
    end
    targets = vcat([header], exit_targets)          # header first, so entry_index 0

    mux = create_mux!(m, targets; absorb=false, extra_types=Any[Int])
    sr_id = mux.extra_ids[1]                          # shouldRepeat

    for r in back_refs;  redirect_edge!(m, mux, r; extra_vals=Any[1]); end
    for r in exit_refs;  redirect_edge!(m, mux, r; extra_vals=Any[0]); end
    live = _live_positions(m, mux, vcat(back_refs, exit_refs))

    latch = mux.mux_id
    cmp = alloc_id!(m); m.types[cmp] = Bool; m.codelocs[cmp] = _NOLOC
    push!(m.blocks[latch].body,
          MStmt(cmp, Expr(:call, Core.:(===), SSAValue(sr_id), 1), Bool, _NOLOC, UInt32(0)))
    header_edge = MEdge(header, slice_vals(mux, header, live))
    exitblk = add_block!(m, MBlock(Int[], MStmt[], MReturn(), _NOLOC))
    m.blocks[latch].term = MCondBr(SSAValue(cmp), header_edge, MEdge(exitblk, Any[]))

    if isempty(exit_targets)
        m.blocks[exitblk].term = MReturn()           # infinite loop: unreachable
    else
        dispatch!(m, mux; excluded=Set{Int}([header]), live, from=exitblk)
    end
    return mux
end

# All SSAValue ids referenced inside `b`: body statement operands, terminator
# operands, and outgoing-edge operands (the values this block contributes to its
# successors' block arguments).
function _mblock_use_ids(b::MBlock)
    ids = Int[]
    collect_ssa(@nospecialize(v)) = (v isa SSAValue && push!(ids, v.id); v)
    for s in b.body
        # A PhiC's operands name UpsilonNode statements (tokens), not values.
        s.stmt isa Core.PhiCNode && continue
        remap_ssa(s.stmt, collect_ssa)
    end
    t = b.term
    if t isa MGoto
        for v in t.edge.args; v isa SSAValue && push!(ids, v.id); end
    elseif t isa MCondBr
        t.cond isa SSAValue && push!(ids, t.cond.id)
        for v in t.t.args; v isa SSAValue && push!(ids, v.id); end
        for v in t.f.args; v isa SSAValue && push!(ids, v.id); end
    elseif t isa MReturn
        t.has_val && t.val isa SSAValue && push!(ids, t.val.id)
    elseif t isa MEnter
        has_scope(t) && t.scope isa SSAValue && push!(ids, t.scope.id)
        for v in t.body.args; v isa SSAValue && push!(ids, v.id); end
    end
    return ids
end

# Apply value-map `f` to every operand of `b`: body statements (via `remap_ssa`),
# terminator operands, and outgoing-edge operands. Mirrors `_mblock_use_ids`.
function _rewrite_mblock!(b::MBlock, f)
    for (i, s) in enumerate(b.body)
        s.stmt isa Core.PhiCNode && continue   # upsilon tokens, not values
        b.body[i] = MStmt(s.id, remap_ssa(s.stmt, f), s.type, s.codeloc, s.flag)
    end
    t = b.term
    if t isa MGoto
        for k in eachindex(t.edge.args); t.edge.args[k] = f(t.edge.args[k]); end
    elseif t isa MCondBr
        for k in eachindex(t.t.args); t.t.args[k] = f(t.t.args[k]); end
        for k in eachindex(t.f.args); t.f.args[k] = f(t.f.args[k]); end
        b.term = MCondBr(f(t.cond), t.t, t.f)
    elseif t isa MReturn
        t.has_val && (b.term = MReturn(f(t.val), true))
    elseif t isa MEnter
        has_scope(t) && (t.scope = f(t.scope))
        for k in eachindex(t.body.args); t.body.args[k] = f(t.body.args[k]); end
    end
end

"""Reduce form (the latch-arg half of MLIR's `transformToReduceLoop`). For every
value defined inside the loop and used outside it, add a latch block argument fed
`value`-or-`undef` from each latch predecessor, and rewrite the outside uses to
that latch arg. An edge feeds the value only when it is an exit edge, the value
dominates it, and the edge's original target (`exit_targets`, recorded before the
edge was redirected to the latch) reaches an outside use of the value without
re-entering the loop. Every other edge feeds `undef`: the latch arg only serves
uses outside the loop, so the value carried around a back edge or out through an
exit that never reads it would only be kept alive for nothing. After this every
loop-internal value read downstream is a latch block arg, so the lift threads it
out as a `BreakOp` result with no escape scan. `LoopOp` has separate
`Break`/`Continue` values, so only this latch-arg half is needed: no header arg,
no exit-block arg.

Excludes the latch's own block args (the mux slices and discriminator already
become loop results through the post-loop dispatch). `loop_blocks` must include
`latch`."""
function reduce_loop!(m::MCFG, header::Int, latch::Int, loop_blocks::Set{Int},
                      exit_targets::Dict{EdgeRef, Int})
    domtree = construct_domtree(build_cfg(m))

    # Definition site and type of each SSA id. Block-arg types live in `m.types`;
    # body-statement types live in the `MStmt`, not `m.types`, so capture both.
    # Otherwise a reduce arg for a body def gets `Any` and breaks the result phi's
    # type.
    def_block = Dict{Int, Int}()
    def_type = Dict{Int, Any}()
    for (bid, b) in enumerate(m.blocks)
        for a in b.args; def_block[a] = bid; def_type[a] = get(m.types, a, Any); end
        for s in b.body; def_block[s.id] = bid; def_type[s.id] = s.type; end
    end

    # Escaping values: loop-internal defs referenced from a non-loop block, in
    # deterministic (block, first-seen) order. The latch's own args are skipped.
    # Also record the blocks using each one. Exit-edge operands are not among
    # them: those edges leave loop blocks and already feed the mux slices.
    latch_args = Set(m.blocks[latch].args)
    escaping = Int[]
    use_blocks = Dict{Int, Set{Int}}()
    for bid in 1:length(m.blocks)
        bid in loop_blocks && continue
        for id in _mblock_use_ids(m.blocks[bid])
            (get(def_block, id, 0) in loop_blocks) || continue
            id in latch_args && continue
            haskey(use_blocks, id) || push!(escaping, id)
            push!(get!(Set{Int}, use_blocks, id), bid)
        end
    end
    isempty(escaping) && return

    # The blocks reachable from each original exit target without re-entering
    # the loop. A path back into the loop runs the latch again, which redefines
    # the latch arg, so a use beyond it never reads the value fed here. Blocks of
    # an enclosing loop count as outside, which can only over-approximate.
    reach = Dict{Int, Set{Int}}()
    for t in unique(values(exit_targets))
        seen = Set{Int}()
        wl = Int[t]
        while !isempty(wl)
            b = pop!(wl)
            (b in seen || b in loop_blocks) && continue
            push!(seen, b)
            append!(wl, _term_targets(m.blocks[b].term))
        end
        reach[t] = seen
    end

    # All edges into the latch (the back + exit edges, post-redirect).
    pred_refs = EdgeRef[]
    for src in 1:length(m.blocks)
        append!(pred_refs, edge_refs(m, src, latch))
    end

    larg_of = Dict{Int, Int}()
    for v in escaping
        T = get(def_type, v, Any)
        larg = alloc_id!(m)
        larg_of[v] = larg
        m.types[larg] = T
        m.codelocs[larg] = get(m.codelocs, v, _NOLOC)
        push!(m.blocks[latch].args, larg)
        dv = def_block[v]
        for ref in pred_refs
            e = edge_of(m, ref)
            t = get(exit_targets, ref, 0)
            feed = t != 0 && dominates(domtree, dv, ref.src) &&
                   !isdisjoint(reach[t], use_blocks[v])
            push!(e.args, feed ? SSAValue(v) : Undef(T))
        end
    end
    # Every outside use, in one pass (the latch args are fresh ids, so no rewrite feeds another,
    # and the edges into the latch leave loop blocks, which are not rewritten).
    fv(@nospecialize(w)) = w isa SSAValue && haskey(larg_of, w.id) ? SSAValue(larg_of[w.id]) : w
    for bid in 1:length(m.blocks)
        bid in loop_blocks && continue
        _rewrite_mblock!(m.blocks[bid], fv)
    end
end

"""Find one natural loop with >=2 exit edges or >=2 back edges and collapse it to
a single-exiting latch in reduce form. The >=2-exit-edge case is a multi-exit
loop; the >=2-back-edge case is a post-entry-mux irreducible loop, whose back
edges the one latch unifies. Returns `true` if it transformed one."""
function normalize_one_loop_latch!(m::MCFG, loops=natural_loops_m(m))
    for h in sort!(collect(keys(loops)))
        body = loops[h]
        back_refs = EdgeRef[]; exit_refs = EdgeRef[]
        for src in sort!(collect(body))
            for r in _edge_refs_of(src, m.blocks[src].term)
                tgt = edge_of(m, r).target
                tgt == h ? push!(back_refs, r) : (tgt ∉ body && push!(exit_refs, r))
            end
        end
        (length(exit_refs) >= 2 || length(back_refs) >= 2) || continue
        exit_targets = Dict(r => edge_of(m, r).target for r in exit_refs)
        mux = single_exiting_latch!(m, h, back_refs, exit_refs)
        reduce_loop!(m, h, mux.mux_id, union(body, Set((mux.mux_id,))), exit_targets)
        return true
    end
    return false
end

#=============================================================================
 Continuation multiplexer.

 A conditional whose two arms reconverge at more than one block (the short-circuit
 shape `if a||b { body }`, where `body` is reached from both arms, and so is the
 merge) has a multi-entry continuation. Route every edge into that continuation
 through one mux so it becomes single-entry; the lift then structurizes it with the
 ordinary IfOp path (no shape-matching). Reuses the lift's own `branch_continuation`
 exclusion analysis (loop-aware) directly on the MBlock CFG.
=============================================================================#

# Minimal LoopCtx for the innermost loop enclosing `E`. `branch_continuation` uses
# only `header`/`loop_blocks`, to skip the loop's back edge and exit edges, which
# are not part of a branch's forward continuation.
function enclosing_loop_ctx(loops::Dict{Int, Set{Int}}, E::Int)
    best_h = 0; best_body = nothing; best_size = typemax(Int)
    for (h, body) in loops
        if E in body && length(body) < best_size
            best_h = h; best_body = body; best_size = length(body)
        end
    end
    best_body === nothing && return nothing
    return LoopCtx(best_h, best_body)
end

"""Find one conditional with a multi-entry continuation and route every edge into
that continuation through one mux (MLIR `createSingleEntryBlock` for the
continuation), making it single-entry. Returns `true` if it muxed one. After this
the lift's ordinary IfOp path handles short-circuits, N-way merges, and nested
gated bodies uniformly, with `find_branch_regions` always finding a singleton
merge."""
function normalize_one_continuation!(m::MCFG, cfg::CFG=build_cfg(m),
                                     domtree::DomTree=construct_domtree(cfg),
                                     loops=natural_loops_m(m, cfg, domtree))
    found = find_continuation(m, cfg, domtree, loops)
    found === nothing && return false
    single_entry_mux!(m, found[2])
    return true
end

"""Dominator-tree preorder of the reachable blocks, siblings by block id."""
function dom_preorder(domtree::DomTree)
    order = Int[]
    stack = [1]
    while !isempty(stack)
        b = pop!(stack)
        push!(order, b)
        append!(stack, sort(domtree.nodes[b].children; rev=true))
    end
    return order
end

"""The first conditional in dominator-tree preorder (siblings by block id), from
and including block `start`, with a multi-entry continuation, and the edges into
that continuation: `(E, refs)`, or `nothing`.

Visiting dominating branches first matters when a branch's continuation edges all
leave one arm: muxed there, the mux joins that arm and its dispatch reproduces the
same entries. A dominating branch that joins those paths with others has to be
muxed first, e.g. a loop's exit dispatch, which block index order visits last
because the latch appends it. Finding a branch whose arm would absorb the mux is
an error."""
function find_continuation(m::MCFG, cfg::CFG, domtree::DomTree, loops; start::Int=1)
    all_blocks = Set(1:length(m.blocks))
    order = dom_preorder(domtree)
    for E in @view order[findfirst(==(start), order):end]
        t = m.blocks[E].term
        t isa MCondBr || continue
        true_dest, false_dest = t.t.target, t.f.target
        lctx = enclosing_loop_ctx(loops, E)
        then_blocks, else_blocks = branch_arms(cfg, domtree, true_dest, false_dest, all_blocks)
        entries, notcont = branch_continuation(cfg, domtree, E, true_dest, false_dest,
                                               then_blocks, else_blocks, all_blocks, lctx)
        length(entries) > 1 || continue

        # The continuation edges: every edge from a branch-region block (notcont)
        # into a continuation entry. Routing them through one mux makes the
        # continuation single-entry. Entries keep their args (a merge may also be
        # reached from inside the continuation), so absorb=false.
        entryset = Set(entries)
        refs = EdgeRef[]
        for b in sort!(collect(notcont)), r in _edge_refs_of(b, m.blocks[b].term)
            edge_of(m, r).target in entryset && push!(refs, r)
        end
        if all(r -> r.src in then_blocks, refs) || all(r -> r.src in else_blocks, refs)
            error("continuation of branch $E would be absorbed by one of its arms")
        end
        return E, refs
    end
    return nothing
end

#=============================================================================
 Loop pre-header.

 A loop header reached by more than one entry edge (an `if/else` before the loop,
 or the absorbed entry-dispatch of an irreducible loop) is also a branch merge.
 Route those entry edges through one pre-header so the header gains a single
 non-back predecessor (MLIR's `newLoopParentBlock`), built here in the mutate
 phase rather than during the lift.
=============================================================================#

"""Find one loop header with >=2 entry edges and route them through a single
pre-header, leaving the back edge on the header. This covers a reducible header
with several outside predecessors as well as an irreducible one.

Making the header single-entry-from-outside lets the lift treat the branch's
continuation as the pre-header (whose args receive the merged entry values, an
`if`/`else` selection or an irreducible discriminator, and feed the loop init)
while the loop results stay on the header's own args. Keeping the two distinct
removes the lift's "merge that is a loop header" special case and avoids returning
an entry value as a loop result.

`absorb=false`, entry edges only: the pre-header forwards into the header's
existing args, and the single-exiting latch still owns back/exit unification.
Runs after irreducible + latch so it sees the final (mux) header."""
function normalize_one_preheader!(m::MCFG, loops=natural_loops_m(m), cfg::CFG=build_cfg(m))
    for h in sort!(collect(keys(loops)))
        body = loops[h]
        entry_refs = EdgeRef[]
        for p in sort!(unique(cfg.blocks[h].preds))
            p ∈ body && continue                      # back edge stays on the header
            append!(entry_refs, edge_refs(m, p, h))
        end
        length(entry_refs) > 1 || continue
        single_entry_mux!(m, entry_refs)              # absorb=false: a pure pre-header
        return true
    end
    return false
end

"""One normalization round: the first pass with something to collapse mutates `m`,
and the round ends. The passes share one CFG, dominator tree and loop analysis,
which any mutation invalidates. The continuation scan resumes at branch `cursor`
(a mux and its dispatch blocks are dominated by the branch, so the branches before
it in preorder are unchanged) and falls back to a scan from the entry. Returns the next round's cursor
(the branch just muxed, or 1 after any other mutation), or `nothing` if `m` is
normalized."""
function normalize_round!(m::MCFG, cursor::Int)
    cfg = build_cfg(m)
    domtree = construct_domtree(cfg)
    normalize_one_irreducible!(m, cfg, domtree) && return 1
    loops = natural_loops_m(m, cfg, domtree)
    normalize_one_loop_latch!(m, loops) && return 1
    found = find_continuation(m, cfg, domtree, loops; start=cursor)
    if found === nothing && cursor > 1
        found = find_continuation(m, cfg, domtree, loops)
    end
    if found !== nothing
        E, refs = found
        single_entry_mux!(m, refs)
        return E
    end
    normalize_one_preheader!(m, loops, cfg) && return 1
    return nothing
end

"""Mutate `m` until no multi-entry situation remains. Each step collapses one
multi-entry header (irreducible), one multi-exit loop (the single-exiting latch +
reduce form), one multi-predecessor branch continuation, or one multi-entry loop
header (the pre-header), with a round limit as a safeguard. The lift then only
ever structurizes single-entry regions."""
function normalize_cf!(m::MCFG)
    limit = 8 * (length(m.blocks) + 16)
    rounds = 0
    cursor = 1
    while (cursor = normalize_round!(m, cursor)) !== nothing
        (rounds += 1) > limit && error("normalize_cf! failed to converge (likely a mux bug)")
    end
    return rounds > 0
end

"""
    normalize_cf(ir::IRCode) -> MCFG

Collapse every multi-entry CFG situation (irreducible loop headers, multi-exit
loops, multi-predecessor continuations) to single-entry via edge multiplexers, so
the lift only structurizes single-entry regions. One `ingest`, then one mutate
fixpoint over the `MCFG`; the lift (`lift_mcfg`) reads the returned `MCFG`
directly.
"""
function normalize_cf(ir::IRCode)
    m = ingest(ir)
    normalize_cf!(m)
    return m
end
