# CFG normalization via edge multiplexers (port of MLIR CFGToSCF's EdgeMultiplexer).
#
# The structurizer lifts only single-entry regions. To get there for the hard
# cases (irreducible multi-entry loop headers and multi-predecessor branch
# continuations, i.e. short-circuits) the CFG is mutated so every such region
# becomes single-entry, then the ordinary lift runs on the result. The mechanism:
# insert a single "multiplexer" block, redirect all incoming edges through it, and
# dispatch from it by an integer discriminator.
#
# We work on a mutable, explicit-edge block form (`MBlock`) carrying stable ids.
# Block arguments and per-edge operands replace SSA phi nodes, so redirecting an
# edge is local; `ingest` converts IRCode's phi-form into this block-argument form.
#
# The mux's N-way dispatch is emitted as a GotoIfNot compare-chain on the
# discriminator, since Julia IR has no switch. The mutated CFG is ordinary
# reducible IR that the existing lift handles with no new concepts; for N=2 the
# chain is a single GotoIfNot, lifting to one IfOp.

# The `MBlock`/`MCFG` type definitions live in `structurize/mcfg.jl`. This file
# holds the operations: `ingest` (the IRCode boundary), the `EdgeMultiplexer`, and
# the `normalize_cf!` mutate fixpoint.

#=============================================================================
 ingest: IRCode -> MCFG  (phi -> block-arg + edge-operands)
=============================================================================#

const _NOLOC = (Int32(0), Int32(0), Int32(0))

# Per-statement debug location, captured at ingest into each `MStmt.codeloc`.
# On 1.12+ this is the `(line, inlined_at, ?)` triple from the `DebugInfoStream`.
# On 1.11 it is the single linetable index `stmts.line[pc]` stashed in slot 1
# (slots 2/3 unused), which `capture_debuginfo` uses to rebuild the SCI line map.
@static if VERSION >= v"1.12-"
    _codeloc(ir::IRCode, pc::Int) = CC.getdebugidx(ir.debuginfo, pc)::NTuple{3, Int32}
else
    _codeloc(ir::IRCode, pc::Int) = (Int32(ir.stmts.line[pc]), Int32(0), Int32(0))
end

"""
    ingest(ir::IRCode) -> MCFG

Convert dense `IRCode` into the explicit-edge mutable form. Leading phi nodes of
each block become block arguments; the values they carry per predecessor become
that predecessor edge's operands. Stable ids == original SSA positions.
"""
function ingest(ir::IRCode)
    di = @static VERSION >= v"1.12-" ? ir.debuginfo : ir.linetable
    nb = length(ir.cfg.blocks)
    blocks = [MBlock() for _ in 1:nb]
    types = Dict{Int, Any}()
    codelocs = Dict{Int, NTuple{3, Int32}}()

    # Per block: parallel to args, the phi's (pred_bb -> value) map. Transient,
    # consumed below to fill edge operands.
    phivals = [Dict{Int, Dict{Int, Any}}() for _ in 1:nb]  # arg_id -> (pred -> value)

    # Pass 1: split each block into args / body / terminator. Edges get empty
    # operand vectors here, filled in pass 2.
    for i in 1:nb
        bb = ir.cfg.blocks[i]
        mb = blocks[i]
        term_stmt = nothing
        last_loc = _NOLOC
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            loc = _codeloc(ir, si)
            last_loc = loc
            if stmt isa PhiNode
                push!(mb.args, si)
                types[si] = ir.stmts.type[si]
                codelocs[si] = loc
                ev = Dict{Int, Any}()
                for (k, edge) in enumerate(stmt.edges)
                    if isassigned(stmt.values, k)
                        ev[Int(edge)] = stmt.values[k]
                    end
                end
                phivals[i][si] = ev
            elseif stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode
                term_stmt = stmt
                mb.term_codeloc = loc
            else
                push!(mb.body, MStmt(si, stmt, ir.stmts.type[si], loc, ir.stmts.flag[si]))
            end
        end
        if term_stmt === nothing            # fallthrough block: goto-next, or
            mb.term_codeloc = last_loc      # unreachable dead-end if last (MReturn)
        end
        mb.term = _ingest_term(term_stmt, i, bb, nb)
    end

    # Pass 2: fill each edge's operands from the target block's phi values.
    for i in 1:nb
        _fill_edge_operands!(blocks[i].term, i, blocks, phivals, types)
    end

    valid_worlds = @static VERSION >= v"1.12-" ? ir.valid_worlds : nothing
    return MCFG(blocks, 1, types, codelocs,
                length(ir.stmts.stmt) + 1,
                copy(ir.argtypes), copy(ir.sptypes), di, valid_worlds)
end

function _ingest_term(term_stmt, i::Int, bb, nb::Int)
    if term_stmt isa ReturnNode
        return isdefined(term_stmt, :val) ? MReturn(term_stmt.val, true) : MReturn()
    elseif term_stmt isa GotoNode
        return MGoto(MEdge(term_stmt.label))
    elseif term_stmt isa GotoIfNot
        false_dest = term_stmt.dest
        true_dest = length(bb.succs) == 1 ? only(bb.succs) :
                    first(s for s in bb.succs if s != false_dest)
        return MCondBr(term_stmt.cond, MEdge(true_dest), MEdge(false_dest))
    else
        # Fallthrough: no terminator. Goto next block, or unreachable if last.
        return i < nb ? MGoto(MEdge(i + 1)) : MReturn()
    end
end

# For each edge i->B, fill operands = [phivals[B][arg].get(i, Undef) for arg in B.args].
# A predecessor with no phi value (a dead/undef edge) carries Undef, becoming an
# unassigned phi slot at emit.
function _fill_edge_operands!(term::MTerm, i::Int, blocks, phivals, types)
    if term isa MGoto
        _fill_edge!(term.edge, i, blocks, phivals, types)
    elseif term isa MCondBr
        _fill_edge!(term.t, i, blocks, phivals, types)
        _fill_edge!(term.f, i, blocks, phivals, types)
    end
end

function _fill_edge!(e::MEdge, src::Int, blocks, phivals, types)
    B = e.target
    1 <= B <= length(blocks) || return
    tgt = blocks[B]
    resize!(e.args, length(tgt.args))
    for (j, arg) in enumerate(tgt.args)
        ev = phivals[B][arg]
        e.args[j] = get(ev, src, Undef(get(types, arg, Any)))
    end
end

#=============================================================================
 capture_debuginfo: MCFG -> (debuginfo table, line_map)

 The SCI resolves a statement's source location from `line_map[ssa_idx]` (negative
 means a direct PC into the table, positive means an anchor to another id to
 follow) plus the table. Both are built from the `MBlock` codelocs, where each
 statement keeps its location at its own stable id.
=============================================================================#

@static if VERSION >= v"1.12-"
    function capture_debuginfo(m::MCFG)
        maxid = m.next_id - 1
        line = fill(Int32(0), max(maxid, 0) * 3)
        line_map = Dict{Int, Int}()
        setloc!(id, loc) = (off = 3 * (id - 1);
                            line[off + 1] = loc[1]; line[off + 2] = loc[2]; line[off + 3] = loc[3])
        for b in m.blocks
            for s in b.body
                setloc!(s.id, s.codeloc); line_map[s.id] = -s.id
            end
            for a in b.args
                setloc!(a, get(m.codelocs, a, _NOLOC)); line_map[a] = -a
            end
        end
        di = CC.DebugInfoStream(line)
        if m.debuginfo isa CC.DebugInfoStream
            di.def = m.debuginfo.def
            di.linetable = m.debuginfo.linetable
            di.edges = copy(m.debuginfo.edges)
        end
        return di, line_map
    end
else
    function capture_debuginfo(m::MCFG)
        line_map = Dict{Int, Int}()
        for b in m.blocks
            for s in b.body
                li = Int(s.codeloc[1]); li != 0 && (line_map[s.id] = -li)
            end
            for a in b.args
                li = Int(get(m.codelocs, a, _NOLOC)[1]); li != 0 && (line_map[a] = -li)
            end
        end
        debuginfo_table = m.debuginfo isa Vector ? copy(m.debuginfo) : Core.LineInfoNode[]
        return debuginfo_table, line_map
    end
end

#=============================================================================
 Duplicate-edge split (run by `lift_mcfg` before the lift)
=============================================================================#

"""A trampoline block `Tr: goto target(args)`. Reached only by an explicit
`GotoNode`/`GotoIfNot`-dest edge, so it has a single predecessor."""
_new_trampoline(target::Int, args::Vector{Any}) =
    MBlock(Int[], MStmt[], MGoto(MEdge(target, args)), _NOLOC)

"""Split any `GotoIfNot` whose two edges target the same block: route the false
edge through a trampoline so the target has two distinct predecessor blocks (a
Julia phi can't list one predecessor twice)."""
function split_duplicate_edges!(m::MCFG)
    for id in 1:length(m.blocks)        # range fixed before trampolines are appended
        t = m.blocks[id].term
        t isa MCondBr || continue
        if t.t.target == t.f.target
            tr = add_block!(m, _new_trampoline(t.f.target, copy(t.f.args)))
            t.f.target = tr
            empty!(t.f.args)
        end
    end
end

#=============================================================================
 EdgeMultiplexer (port of CFGToSCF.cpp EdgeMultiplexer::create/redirectEdge/
 createSwitch). One block that all incoming edges are routed through; it
 dispatches to the original distinct targets ("entries") by an integer
 discriminator. The dispatch is a GotoIfNot compare-chain (Julia has no switch)
 with the last entry as the default. This makes every multi-entry situation
 single-entry: each entry ends up with the mux as its only predecessor.
=============================================================================#

"""A reference to one outgoing edge of a block: which terminator slot it is.
`:goto` (a `MGoto`), `:t` (a `MCondBr` true edge), or `:f` (a `MCondBr` false edge)."""
struct EdgeRef
    src::Int
    slot::Symbol     # :goto | :t | :f
end

function edge_of(m::MCFG, r::EdgeRef)
    t = m.blocks[r.src].term
    r.slot === :goto ? (t::MGoto).edge :
    r.slot === :t ? (t::MCondBr).t : (t::MCondBr).f
end

"""All edge references from `src` to `target` (a CondBr may yield two)."""
function edge_refs(m::MCFG, src::Int, target::Int)
    t = m.blocks[src].term
    refs = EdgeRef[]
    if t isa MGoto
        t.edge.target == target && push!(refs, EdgeRef(src, :goto))
    elseif t isa MCondBr
        t.t.target == target && push!(refs, EdgeRef(src, :t))
        t.f.target == target && push!(refs, EdgeRef(src, :f))
    end
    return refs
end

"""The created multiplexer: its block id, the distinct entries (in order), the
per-entry argument-slice offset into the mux's args, the discriminator arg id
(0 if a single entry), and any extra arg ids appended at the tail.

`absorb` selects between two roles. When `true` (a loop-header mux, whose entries
are dispatch arms reached only from the mux, e.g. irreducible headers) the mux
reuses the entries' own arg ids and the entries are left arg-less, so each entry's
body references the mux's carries directly and the dispatch passes nothing. When
`false` (a branch-continuation mux, where an entry may also be reached from inside
the continuation, e.g. a short-circuit merge) the mux's slice args are fresh and
the dispatch forwards them into the entries' phis for the merge-phi machinery to
resolve."""
struct EdgeMux
    mux_id::Int
    entries::Vector{Int}
    offset::Dict{Int, Int}
    nargs::Dict{Int, Int}
    arg_ids::Vector{Int}
    disc_id::Int
    extra_ids::Vector{Int}
    absorb::Bool
end

entry_index(mux::EdgeMux, e::Int) = findfirst(==(e), mux.entries)::Int - 1   # 0-based
# Values the dispatch forwards to entry `e`. Empty under `absorb`, since the entry
# has no args and its body reads the mux's carries directly. `live` is the set of
# mux arg positions that some redirected edge assigned a real (non-`Undef`) value;
# a position absent from `live` is forwarded as `Undef`, since its mux phi would be
# empty (e.g. a value only the body defines, never the skipped continuation entry).
function slice_vals(mux::EdgeMux, e::Int, live::Union{Nothing, Set{Int}})
    mux.absorb && return Any[]
    off = mux.offset[e]
    # `Undef`'s type is discarded at emit (it becomes an unassigned phi slot).
    return Any[(live === nothing || (off + k) in live) ?
               SSAValue(mux.arg_ids[off + k]) : Undef(Any) for k in 1:mux.nargs[e]]
end

"""Create a multiplexer block for the distinct targets of `entry_list`. Its
arguments are the union of the entries' block arguments (each entry's slice
recorded by offset), followed by a discriminator (only if >1 distinct entry),
followed by `extra_types` block args. See [`EdgeMux`](@ref) for `absorb`. Does
not yet redirect edges or dispatch; see [`redirect_edge!`](@ref) and
[`dispatch!`](@ref)."""
function create_mux!(m::MCFG, entry_list::Vector{Int}; absorb::Bool=false,
                     extra_types::Vector=Any[])
    entries = Int[]
    for e in entry_list
        e in entries || push!(entries, e)
    end
    @assert !isempty(entries) "mux needs at least one entry"

    arg_ids = Int[]
    offset = Dict{Int, Int}()
    nargs = Dict{Int, Int}()
    for e in entries
        offset[e] = length(arg_ids)
        ea = copy(m.blocks[e].args)
        nargs[e] = length(ea)
        if absorb
            append!(arg_ids, ea)            # reuse the entry's arg ids as carries
            empty!(m.blocks[e].args)        # entry becomes arg-less
        else
            for a in ea
                id = alloc_id!(m)
                m.types[id] = get(m.types, a, Any)
                m.codelocs[id] = get(m.codelocs, a, _NOLOC)
                push!(arg_ids, id)
            end
        end
    end

    disc_id = 0
    if length(entries) > 1
        disc_id = alloc_id!(m)
        m.types[disc_id] = Int
        m.codelocs[disc_id] = _NOLOC
        push!(arg_ids, disc_id)
    end

    extra_ids = Int[]
    for T in extra_types
        id = alloc_id!(m)
        m.types[id] = T
        m.codelocs[id] = _NOLOC
        push!(arg_ids, id)
        push!(extra_ids, id)
    end

    mux_id = add_block!(m, MBlock(copy(arg_ids), MStmt[], MReturn(), _NOLOC))
    return EdgeMux(mux_id, entries, offset, nargs, arg_ids, disc_id, extra_ids, absorb)
end

"""Redirect `ref` through the mux: write its real operands into its target
entry's slot, the entry's index into the discriminator, `extra_vals` into the
extra slots, and `Undef` into every other entry's slot (the discriminator
guarantees that slot is never read on this path). Points the edge at the mux."""
function redirect_edge!(m::MCFG, mux::EdgeMux, ref::EdgeRef; extra_vals::Vector=Any[])
    e = edge_of(m, ref)
    target = e.target
    haskey(mux.offset, target) || error("redirect: edge target BB$target is not a mux entry")
    @assert length(extra_vals) == length(mux.extra_ids)

    orig = copy(e.args)
    newops = Any[Undef(get(m.types, id, Any)) for id in mux.arg_ids]
    off = mux.offset[target]
    for k in 1:mux.nargs[target]
        newops[off + k] = orig[k]
    end
    if mux.disc_id != 0
        newops[findfirst(==(mux.disc_id), mux.arg_ids)] = entry_index(mux, target)
    end
    for (j, id) in enumerate(mux.extra_ids)
        newops[findfirst(==(id), mux.arg_ids)] = extra_vals[j]
    end
    e.target = mux.mux_id
    e.args = newops
end

"""Emit the mux's dispatch: an integer compare-chain on the discriminator that
branches to each entry (forwarding that entry's argument slice), the last entry
serving as the default. Entries in `excluded` are left out (used by the latch,
which dispatches them through a separate back edge). `live` (see `slice_vals`)
restricts which slice positions are forwarded by value vs as `Undef`."""
function dispatch!(m::MCFG, mux::EdgeMux; excluded::Set{Int}=Set{Int}(),
                   live::Union{Nothing, Set{Int}}=nothing, from::Int=mux.mux_id)
    targets = [e for e in mux.entries if !(e in excluded)]
    @assert !isempty(targets) "dispatch has no targets"

    if length(targets) == 1
        m.blocks[from].term = MGoto(MEdge(targets[1], slice_vals(mux, targets[1], live)))
        return
    end

    disc = mux.disc_id
    cur = from
    for i in 1:length(targets) - 1
        e = targets[i]
        cmp = alloc_id!(m)
        m.types[cmp] = Bool
        m.codelocs[cmp] = _NOLOC
        push!(m.blocks[cur].body,
              MStmt(cmp, Expr(:call, Core.:(===), SSAValue(disc), entry_index(mux, e)),
                    Bool, _NOLOC, UInt32(0)))
        t_edge = MEdge(e, slice_vals(mux, e, live))
        if i < length(targets) - 1
            nxt = add_block!(m, MBlock(Int[], MStmt[], MReturn(), _NOLOC))
            m.blocks[cur].term = MCondBr(SSAValue(cmp), t_edge, MEdge(nxt, Any[]))
            cur = nxt
        else
            last = targets[end]
            m.blocks[cur].term = MCondBr(SSAValue(cmp), t_edge, MEdge(last, slice_vals(mux, last, live)))
        end
    end
end

# Mux arg positions that some incoming (redirected) edge assigned a real value.
# A position never assigned is dead: its phi would be empty, so the dispatch
# forwards `Undef` for it instead of referencing the empty phi.
function _live_positions(m::MCFG, mux::EdgeMux, refs::Vector{EdgeRef})
    live = Set{Int}()
    for r in refs
        for (i, v) in enumerate(edge_of(m, r).args)
            v isa Undef || push!(live, i)
        end
    end
    return live
end

"""Route every edge in `edge_refs_list` through a fresh mux for their distinct
targets, then emit the dispatch (MLIR's `createSingleEntryBlock`). Returns the
mux. `extra_types`/`extra_for` supply the type and per-edge value of an extra
carried arg (the latch's `shouldRepeat`); `excluded` entries are left out of the
dispatch."""
function single_entry_mux!(m::MCFG, edge_refs_list::Vector{EdgeRef};
                           absorb::Bool=false,
                           extra_types::Vector=Any[],
                           extra_for::Function=(_ -> Any[]),
                           excluded::Set{Int}=Set{Int}())
    targets = Int[]
    for r in edge_refs_list
        t = edge_of(m, r).target
        t in targets || push!(targets, t)
    end
    mux = create_mux!(m, targets; absorb, extra_types)
    for r in edge_refs_list
        redirect_edge!(m, mux, r; extra_vals=extra_for(r))
    end
    live = _live_positions(m, mux, edge_refs_list)
    dispatch!(m, mux; excluded, live)
    return mux
end

#=============================================================================
 normalize_cf: the mutate-then-lift driver.

 Repeatedly find one multi-entry situation and collapse it to single-entry with an
 EdgeMultiplexer, until none remain. The lift (`structurize_region!`) then only
 ever sees single-entry regions.
=============================================================================#

_term_targets(t::MGoto) = (t.edge.target,)
_term_targets(t::MCondBr) = (t.t.target, t.f.target)
_term_targets(t::MReturn) = ()

"""A lightweight `CFG` over the mutable blocks (preds/succs only; statement
ranges are placeholders) for dominance / SCC queries during normalization. Block
indices equal MBlock ids, so results map straight back."""
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
function normalize_one_irreducible!(m::MCFG)
    cfg = build_cfg(m)
    domtree = construct_domtree(cfg)
    reach = CFGReachability(cfg, domtree)
    nb = length(m.blocks)

    by_scc = Dict{Int, Vector{Int}}()
    for bb in 1:nb
        # `reach.irreducible` is a compiler-internal BitArray on 1.11 whose
        # `getindex` is only visible inside `Core.Compiler`; index it through CC
        # (works on 1.12's plain BitVector too).
        CC.getindex(reach.irreducible, bb) && push!(get!(Vector{Int}, by_scc, reach.scc[bb]), bb)
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
function natural_loops_m(m::MCFG)
    cfg = build_cfg(m)
    domtree = construct_domtree(cfg)
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
    end
    return ids
end

# Apply value-map `f` to every operand of `b`: body statements (via `remap_ssa`),
# terminator operands, and outgoing-edge operands. Mirrors `_mblock_use_ids`.
function _rewrite_mblock!(b::MBlock, f)
    for (i, s) in enumerate(b.body)
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
    end
end

"""Reduce form (the latch-arg half of MLIR's `transformToReduceLoop`). For every
value defined inside the loop and used outside it, add a latch block argument fed
`value`-or-`undef` from each latch predecessor by dominance, and rewrite the
outside uses to that latch arg. After this every loop-internal value read
downstream is a latch block arg, so the lift threads it out as a `BreakOp` result
with no escape scan. `LoopOp` has separate `Break`/`Continue` values, so only this
latch-arg half is needed: no header arg, no exit-block arg.

Excludes the latch's own block args (the mux slices and discriminator already
become loop results through the post-loop dispatch). `loop_blocks` must include
`latch`."""
function reduce_loop!(m::MCFG, header::Int, latch::Int, loop_blocks::Set{Int})
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
    latch_args = Set(m.blocks[latch].args)
    escaping = Int[]
    seen = Set{Int}()
    for bid in 1:length(m.blocks)
        bid in loop_blocks && continue
        for id in _mblock_use_ids(m.blocks[bid])
            (get(def_block, id, 0) in loop_blocks) || continue
            (id in latch_args || id in seen) && continue
            push!(escaping, id); push!(seen, id)
        end
    end
    isempty(escaping) && return

    # All edges into the latch (the back + exit edges, post-redirect).
    pred_refs = EdgeRef[]
    for src in 1:length(m.blocks)
        append!(pred_refs, edge_refs(m, src, latch))
    end

    for v in escaping
        T = get(def_type, v, Any)
        larg = alloc_id!(m)
        m.types[larg] = T
        m.codelocs[larg] = get(m.codelocs, v, _NOLOC)
        push!(m.blocks[latch].args, larg)
        dv = def_block[v]
        for ref in pred_refs
            e = edge_of(m, ref)
            push!(e.args, dominates(domtree, dv, ref.src) ? SSAValue(v) : Undef(T))
        end
        fv(@nospecialize(w)) = (w isa SSAValue && w.id == v) ? SSAValue(larg) : w
        for bid in 1:length(m.blocks)
            bid in loop_blocks && continue
            _rewrite_mblock!(m.blocks[bid], fv)
        end
    end
end

"""Find one natural loop with >=2 exit edges or >=2 back edges and collapse it to
a single-exiting latch in reduce form. The >=2-exit-edge case is a multi-exit
loop; the >=2-back-edge case is a post-entry-mux irreducible loop, whose back
edges the one latch unifies. Returns `true` if it transformed one."""
function normalize_one_loop_latch!(m::MCFG)
    loops = natural_loops_m(m)
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
        mux = single_exiting_latch!(m, h, back_refs, exit_refs)
        reduce_loop!(m, h, mux.mux_id, union(body, Set((mux.mux_id,))))
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
    return LoopCtx(best_h, best_body, IRValue[], IRValue[])
end

"""Find one conditional with a multi-entry continuation and route every edge into
that continuation through one mux (MLIR `createSingleEntryBlock` for the
continuation), making it single-entry. Returns `true` if it muxed one. After this
the lift's ordinary IfOp path handles short-circuits, N-way merges, and nested
gated bodies uniformly, with `find_branch_regions` always finding a singleton
merge."""
function normalize_one_continuation!(m::MCFG)
    cfg = build_cfg(m)
    domtree = construct_domtree(cfg)
    loops = natural_loops_m(m)
    all_blocks = Set(1:length(m.blocks))
    for E in 1:length(m.blocks)
        t = m.blocks[E].term
        t isa MCondBr || continue
        true_dest, false_dest = t.t.target, t.f.target
        lctx = enclosing_loop_ctx(loops, E)
        then_blocks, else_blocks, _ =
            find_branch_regions(cfg, domtree, E, true_dest, false_dest, all_blocks, lctx)
        entries, notcont = branch_continuation(cfg, domtree, E, true_dest, false_dest,
                                               then_blocks, else_blocks, all_blocks, lctx)
        length(entries) > 1 || continue

        # The continuation edges: every edge from a branch-region block (notcont)
        # into a continuation entry. Routing them through one mux makes the
        # continuation single-entry. Entries keep their args (a merge may also be
        # reached from inside the continuation), so absorb=false.
        entryset = Set(entries)
        refs = EdgeRef[]
        for b in sort!(collect(notcont)), succ in cfg.blocks[b].succs
            succ in entryset && append!(refs, edge_refs(m, b, succ))
        end
        single_entry_mux!(m, refs)
        return true
    end
    return false
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
function normalize_one_preheader!(m::MCFG)
    loops = natural_loops_m(m)
    cfg = build_cfg(m)
    for h in sort!(collect(keys(loops)))
        body = loops[h]
        entry_refs = EdgeRef[]
        for p in sort!(collect(cfg.blocks[h].preds))
            p ∈ body && continue                      # back edge stays on the header
            append!(entry_refs, edge_refs(m, p, h))
        end
        length(entry_refs) > 1 || continue
        single_entry_mux!(m, entry_refs)              # absorb=false: a pure pre-header
        return true
    end
    return false
end

"""Mutate `m` until no multi-entry situation remains. Each step collapses one
multi-entry header (irreducible), one multi-exit loop (the single-exiting latch +
reduce form), one multi-predecessor branch continuation, or one multi-entry loop
header (the pre-header). All strictly reduce the remaining count (the mux block is
single-entry by construction), so this terminates. The lift then only ever
structurizes single-entry regions."""
function normalize_cf!(m::MCFG)
    changed = false
    guard = 0
    limit = length(m.blocks) + 16
    while normalize_one_irreducible!(m) || normalize_one_loop_latch!(m) ||
          normalize_one_continuation!(m) || normalize_one_preheader!(m)
        changed = true
        guard += 1
        guard > 8 * limit && error("normalize_cf! failed to converge (likely a mux bug)")
    end
    return changed
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

"""
    lift_mcfg(m::MCFG; validate=true, promote=true) -> StructuredIRCode

Lift a normalized `MCFG` to a `StructuredIRCode`. `split_duplicate_edges!` first
routes any `GotoIfNot` whose two edges target the same block through a trampoline,
so every predecessor reaches a block by at most one edge (the lift reads "what
predecessor P contributes" as a single edge operand; a `cond ? a : b` shape needs
the two predecessors distinct). Debug info comes from the `MBlock` codelocs.
"""
function lift_mcfg(m::MCFG; validate::Bool=true, promote::Bool=true)
    split_duplicate_edges!(m)
    debuginfo_table, line_map = capture_debuginfo(m)
    valid_worlds = m.valid_worlds isa WorldRange ? m.valid_worlds :
                   WorldRange(typemin(UInt), typemax(UInt))
    sci = StructuredIRCode(copy(m.argtypes), copy(m.sptypes), Block(), 0, 0,
                           debuginfo_table, line_map, valid_worlds)
    entry, max_ssa, max_arg, updated_line_map = structurize(m, line_map; promote)
    sci.entry = entry
    sci.max_ssa_idx = max_ssa
    sci.max_arg_idx = max_arg
    merge!(sci.line_map, updated_line_map)

    # Parent chain (entry to SCI, sub-blocks to containing block) after structurize
    # and promote, since promote_loops! replaces block.body without going through
    # push!.
    sci.entry.parent = sci
    fix_parents!(sci.entry)

    if validate
        validate_scf(sci.entry)
        validate_no_phis(sci.entry)
        validate_terminators(sci)
        validate_ssa_defs(sci)
        validate_ssa_uniqueness(sci)
    end
    return sci
end
