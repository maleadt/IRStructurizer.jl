# Mutate-then-lift CFG normalization (MLIR CFGToSCF's EdgeMultiplexer).
#
# The structurizer lifts only *single-entry* regions. To get there for the hard
# cases — irreducible (multi-entry) loop headers and multi-predecessor branch
# continuations (short-circuits) — we first MUTATE the CFG so every such region
# becomes single-entry, then run the ordinary lift on the result. This is MLIR's
# architecture (`CFGToSCF.cpp`): insert a single "multiplexer" block, redirect all
# the incoming edges through it, and dispatch from it by an integer discriminator.
#
# Julia's `IRCode` is dense (SSA value == position) and fallthrough-sensitive
# (`GotoIfNot` falls through to the next block on `true`), so "mutate the CFG"
# means "rebuild the IRCode". We work on a mutable, explicit-edge block form
# (`MBlock`) carrying *stable ids* through mutation, and only remap stable→dense
# at `emit`. Block arguments + per-edge operands replace SSA phi nodes here (the
# MLIR model), so redirecting an edge is local — `ingest`/`emit` are the only two
# places that convert between phi-form and block-argument-form.
#
# The mux's N-way dispatch is emitted as a compare-chain of `GotoIfNot` on the
# discriminator (Julia IR has no switch). The mutated CFG is therefore ordinary
# reducible IRCode that the existing lift handles with no new concepts; for N=2
# the chain is a single `GotoIfNot` → one `IfOp`.

#=============================================================================
 Explicit-edge mutable CFG
=============================================================================#

"""An edge to a target block, carrying the operands for the target's block
arguments (one per arg, in order). Operands are `SSAValue`/`Argument`/constant/
`Undef`. `Undef` becomes an unassigned phi slot at `emit`."""
mutable struct MEdge
    target::Int            # MBlock id
    args::Vector{Any}      # successor operands, parallel to target's block args
end
MEdge(target::Int) = MEdge(target, Any[])

# Terminators with explicit edges (no fallthrough reliance).
struct MGoto;   edge::MEdge;                       end
struct MCondBr; cond::Any; t::MEdge; f::MEdge;      end   # GotoIfNot: true=t, false=f
struct MReturn; val::Any; has_val::Bool;           end    # ReturnNode(val) / ReturnNode()
const MTerm = Union{MGoto, MCondBr, MReturn}

MReturn() = MReturn(nothing, false)        # unreachable / throw dead-end

"""A statement in a block body: stable id, statement, type, debug codeloc, and
the `IR_FLAG_*` bitmask carried over from the source IRCode."""
struct MStmt
    id::Int
    stmt::Any
    type::Any
    codeloc::NTuple{3, Int32}
    flag::UInt32
end

"""A basic block in explicit-edge form: block arguments (the SSA ids that were
phi nodes), body statements, and a terminator with explicit edges.
`term_codeloc` is the debug location to attach to the emitted terminator."""
mutable struct MBlock
    args::Vector{Int}      # stable ids of block arguments (were phi results)
    body::Vector{MStmt}
    term::MTerm
    term_codeloc::NTuple{3, Int32}
    term_type::Any         # terminator's type; `Union{}` marks an unreachable/throw dead-end
end
MBlock() = MBlock(Int[], MStmt[], MReturn(), (Int32(0), Int32(0), Int32(0)), Any)

"""The whole mutable CFG. Blocks are indexed by id == position in `blocks`; the
vector only ever grows (mux/trampoline blocks appended), so ids are stable.
`types`/`codelocs` cover block-argument and synthesized ids; body-statement
types/codelocs live in the `MStmt`s."""
mutable struct MCFG
    blocks::Vector{MBlock}
    entry::Int
    order::Vector{Int}                 # logical block order (preserved across emit)
    types::Dict{Int, Any}              # id → type (block args + synthesized stmts)
    codelocs::Dict{Int, NTuple{3, Int32}}  # id → codeloc (block args + synthesized)
    flags::Dict{Int, UInt32}           # id → IR_FLAG_* bitmask (block args)
    next_id::Int                       # next fresh stable id
    # carried through for emit
    argtypes::Vector{Any}
    sptypes::Vector{Any}
    debuginfo::Any
    valid_worlds::Any
end

alloc_id!(m::MCFG) = (id = m.next_id; m.next_id += 1; id)

"""Append a new block, returning its id. Placed last in the logical order unless
`order=false` (used for fallthrough trampolines, which `emit` places inline)."""
function add_block!(m::MCFG, b::MBlock; order::Bool=true)
    push!(m.blocks, b)
    id = length(m.blocks)
    order && push!(m.order, id)
    return id
end

#=============================================================================
 ingest: IRCode → MCFG  (phi → block-arg + edge-operands)
=============================================================================#

const _NOLOC = (Int32(0), Int32(0), Int32(0))

@static if VERSION >= v"1.12-"
    _codeloc(di, pc::Int) = CC.getdebugidx(di, pc)::NTuple{3, Int32}
else
    _codeloc(di, pc::Int) = _NOLOC
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
    flags = Dict{Int, UInt32}()

    # Per block: parallel to args, the phi's (pred_bb → value) map. Transient,
    # consumed below to fill edge operands.
    phivals = [Dict{Int, Dict{Int, Any}}() for _ in 1:nb]  # arg_id → (pred → value)

    # Pass 1: split each block into args / body / terminator (edges with empty
    # operand vectors; filled in pass 2).
    for i in 1:nb
        bb = ir.cfg.blocks[i]
        mb = blocks[i]
        term_stmt = nothing
        last_loc = _NOLOC
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            loc = _codeloc(di, si)
            last_loc = loc
            if stmt isa PhiNode
                push!(mb.args, si)
                types[si] = ir.stmts.type[si]
                codelocs[si] = loc
                flags[si] = ir.stmts.flag[si]
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
                mb.term_type = ir.stmts.type[si]
            else
                push!(mb.body, MStmt(si, stmt, ir.stmts.type[si], loc, ir.stmts.flag[si]))
            end
        end
        if term_stmt === nothing            # fallthrough block
            mb.term_codeloc = last_loc
            mb.term_type = i < nb ? Any : Union{}   # goto-next, or unreachable dead-end
        end
        mb.term = _ingest_term(term_stmt, i, bb, nb)
    end

    # Pass 2: fill each edge's operands from the target block's phi values.
    for i in 1:nb
        _fill_edge_operands!(blocks[i].term, i, blocks, phivals, types)
    end

    valid_worlds = @static VERSION >= v"1.12-" ? ir.valid_worlds : nothing
    return MCFG(blocks, 1, collect(1:nb), types, codelocs, flags,
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

# For each edge i→B, fill operands = [phivals[B][arg].get(i, Undef) for arg in B.args].
# A predecessor with no phi value (a dead/undef edge) carries Undef → becomes an
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
 emit: MCFG → IRCode  (block-arg + edge-operands → phi)
=============================================================================#

"""A trampoline block `Tr: goto target(args)`. Reached only by an explicit
`GotoNode`/`GotoIfNot`-dest edge (never fallthrough), so its placement is free."""
_new_trampoline(target::Int, args::Vector{Any}) =
    MBlock(Int[], MStmt[], MGoto(MEdge(target, args)), _NOLOC, Any)

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

"""Build the emit order from `m.order`, preserving it exactly and inserting a
fallthrough trampoline only where a `GotoIfNot`'s true target is not already the
next block (Julia's `GotoIfNot` falls through to the next block on `true`). On
un-mutated input the original order is fallthrough-correct, so this is identity;
mutation (mux/redirect) is the only source of trampolines."""
function layout!(m::MCFG)
    seq = Int[]
    base = m.order
    for (idx, id) in enumerate(base)
        push!(seq, id)
        t = m.blocks[id].term
        t isa MCondBr || continue
        next_id = idx < length(base) ? base[idx + 1] : 0
        if t.t.target != next_id
            e = t.t                     # reroute true edge through a trampoline
            tr = add_block!(m, _new_trampoline(e.target, copy(e.args)); order=false)
            e.target = tr; empty!(e.args)
            push!(seq, tr)
        end
    end
    return seq
end

# All (predecessor id, edge operands) pairs targeting each block, in placed order.
function _incoming_edges(m::MCFG, order::Vector{Int})
    incoming = Dict{Int, Vector{Tuple{Int, Vector{Any}}}}()
    for id in order
        t = m.blocks[id].term
        if t isa MGoto
            push!(get!(Vector{Tuple{Int, Vector{Any}}}, incoming, t.edge.target), (id, t.edge.args))
        elseif t isa MCondBr
            push!(get!(Vector{Tuple{Int, Vector{Any}}}, incoming, t.t.target), (id, t.t.args))
            push!(get!(Vector{Tuple{Int, Vector{Any}}}, incoming, t.f.target), (id, t.f.args))
        end
    end
    return incoming
end

# A shallow-enough copy for emit: duplicate the mutable spine (blocks, their
# terminators and edges, the order) so emit's trampoline insertion/redirection
# doesn't touch the caller's MCFG. The id→type/codeloc/flag dicts are read-only
# during emit and are shared.
_copy_edge(e::MEdge) = MEdge(e.target, copy(e.args))
_copy_term(t::MGoto) = MGoto(_copy_edge(t.edge))
_copy_term(t::MCondBr) = MCondBr(t.cond, _copy_edge(t.t), _copy_edge(t.f))
_copy_term(t::MReturn) = t
_copy_block(b::MBlock) = MBlock(copy(b.args), copy(b.body), _copy_term(b.term),
                                b.term_codeloc, b.term_type)
function _copy_for_emit(m::MCFG)
    MCFG(MBlock[_copy_block(b) for b in m.blocks], m.entry, copy(m.order),
         m.types, m.codelocs, m.flags, m.next_id,
         m.argtypes, m.sptypes, m.debuginfo, m.valid_worlds)
end

"""
    emit(m::MCFG) -> IRCode

Rebuild a dense `IRCode` from the mutable form. Chooses a fallthrough-preserving
block order (inserting trampolines as needed), reconstructs phi nodes from block
arguments + per-edge operands, remaps stable ids to dense positions, and rebuilds
the CFG and debug info. Non-mutating: operates on a private copy of `m`.
"""
function emit(m_in::MCFG)
    m = _copy_for_emit(m_in)
    split_duplicate_edges!(m)
    order = layout!(m)
    incoming = _incoming_edges(m, order)

    # Dense position assignment: per block, [args (phis)..., body..., terminator].
    bb_of = Dict{Int, Int}()       # mblock id → final BB index
    pos_of = Dict{Int, Int}()      # stable id → dense position
    nstmts = 0
    for (bi, id) in enumerate(order)
        bb_of[id] = bi
        b = m.blocks[id]
        for a in b.args; nstmts += 1; pos_of[a] = nstmts; end
        for s in b.body; nstmts += 1; pos_of[s.id] = nstmts; end
        nstmts += 1                # terminator
    end

    remap_val(@nospecialize(v)) = v isa SSAValue ? SSAValue(pos_of[v.id]) : v
    remap_stmt(@nospecialize(s)) = _remap_stmt(s, remap_val)

    all_stmts = Vector{Any}(undef, nstmts)
    all_types = Vector{Any}(undef, nstmts)
    all_flags = fill(UInt32(0), nstmts)
    line = fill(Int32(0), nstmts * 3)
    bb_ranges = UnitRange{Int}[]

    pos = 0
    setloc!(p, loc) = (off = 3*(p-1); line[off+1] = loc[1]; line[off+2] = loc[2]; line[off+3] = loc[3])
    for id in order
        b = m.blocks[id]
        start = pos + 1
        # Phis from block arguments. A predecessor whose operand is `Undef` is
        # omitted (an unlisted phi edge = undef on that path), reproducing the
        # original phi's edge set; the discriminator guarantees no live path reads
        # an omitted slot.
        for (j, a) in enumerate(b.args)
            phi = PhiNode(Int32[], Any[])
            for (src, ops) in get(incoming, id, Tuple{Int, Vector{Any}}[])
                ops[j] isa Undef && continue
                push!(phi.edges, Int32(bb_of[src]))
                push!(phi.values, remap_val(ops[j]))
            end
            pos += 1
            all_stmts[pos] = phi
            all_types[pos] = get(m.types, a, Any)
            all_flags[pos] = get(m.flags, a, UInt32(0))
            setloc!(pos, get(m.codelocs, a, _NOLOC))
        end
        # Body.
        for s in b.body
            pos += 1
            all_stmts[pos] = remap_stmt(s.stmt)
            all_types[pos] = s.type
            all_flags[pos] = s.flag
            setloc!(pos, s.codeloc)
        end
        # Terminator.
        pos += 1
        all_stmts[pos] = _emit_term(b.term, bb_of, remap_val)
        all_types[pos] = b.term_type
        setloc!(pos, b.term_codeloc)
        push!(bb_ranges, start:pos)
    end

    return _assemble(m, all_stmts, all_types, all_flags, line, bb_ranges, order)
end

# Reconstruct a terminator statement from the explicit-edge form. A CondBr's true
# target is guaranteed (by layout!) to be the next block → GotoIfNot fallthrough.
function _emit_term(t::MTerm, bb_of, remap_val)
    if t isa MGoto
        return GotoNode(bb_of[t.edge.target])
    elseif t isa MCondBr
        return GotoIfNot(remap_val(t.cond), bb_of[t.f.target])
    else  # MReturn
        return t.has_val ? ReturnNode(remap_val(t.val)) : ReturnNode()
    end
end

function _remap_stmt(@nospecialize(stmt), remap_val)
    if stmt isa Expr
        return Expr(stmt.head, Any[remap_val(a) for a in stmt.args]...)
    elseif stmt isa PiNode
        return PiNode(remap_val(stmt.val), stmt.typ)
    elseif stmt isa SSAValue
        return remap_val(stmt)
    elseif stmt isa PhiNode
        new_vals = Vector{Any}(undef, length(stmt.values))
        for k in eachindex(stmt.values)
            isassigned(stmt.values, k) && (new_vals[k] = remap_val(stmt.values[k]))
        end
        return PhiNode(copy(stmt.edges), new_vals)
    else
        return stmt
    end
end

# Build the CFG (preds/succs) and IRCode from the flat statement arrays.
function _assemble(m::MCFG, all_stmts, all_types, all_flags, line, bb_ranges, order)
    n = length(all_stmts)
    nb = length(bb_ranges)
    bb_blocks = BasicBlock[]
    cfg_index = Int[]                       # first stmt of blocks 2..nb (length nb-1)
    for (i, r) in enumerate(bb_ranges)
        push!(bb_blocks, BasicBlock(StmtRange(first(r), last(r)), Int[], Int[]))
        i > 1 && push!(cfg_index, first(r))
    end
    for (i, r) in enumerate(bb_ranges)
        last_s = all_stmts[last(r)]
        if last_s isa GotoNode
            _cfg_edge!(bb_blocks, i, last_s.label)
        elseif last_s isa GotoIfNot
            _cfg_edge!(bb_blocks, i, last_s.dest)
            i < nb && _cfg_edge!(bb_blocks, i, i + 1)
        elseif last_s isa ReturnNode
            # no successors
        else
            i < nb && _cfg_edge!(bb_blocks, i, i + 1)
        end
    end
    cfg = CFG(bb_blocks, cfg_index)

    info = Vector{CC.CallInfo}(undef, n)
    fill!(info, CC.NoCallInfo())
    stmts = InstructionStream(all_stmts, all_types, info, line, all_flags)

    meta = Expr[]
    @static if VERSION >= v"1.12-"
        debuginfo = CC.DebugInfoStream(line)
        if m.debuginfo isa CC.DebugInfoStream
            debuginfo.def = m.debuginfo.def
            debuginfo.linetable = m.debuginfo.linetable
            debuginfo.edges = copy(m.debuginfo.edges)
        end
        return IRCode(stmts, cfg, debuginfo, copy(m.argtypes), meta, CC.VarState[s for s in m.sptypes])
    else
        linetable = m.debuginfo isa Vector ? copy(m.debuginfo) : Core.LineInfoNode[]
        return IRCode(stmts, cfg, linetable, copy(m.argtypes), meta, CC.VarState[s for s in m.sptypes])
    end
end

#=============================================================================
 EdgeMultiplexer  (port of CFGToSCF.cpp EdgeMultiplexer::create/redirectEdge/
 createSwitch). One block that all incoming edges are routed through; it
 dispatches to the original distinct targets ("entries") by an integer
 discriminator. The dispatch is a GotoIfNot compare-chain (Julia has no switch),
 last entry = default. This collapses every multi-entry/-predecessor situation
 to single-entry: each entry ends up with the mux as its only predecessor.
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

`absorb` distinguishes the two roles. When `true` (a loop-header mux: the entries
are dispatch arms reached *only* from the mux, e.g. irreducible headers), the
mux reuses the entries' own arg ids and the entries are left arg-less, so each
entry's body references the mux's carries directly — the dispatch passes nothing
(disc-as-carried-value). When `false` (a branch-continuation mux: an entry may
also be reached from inside the continuation, e.g. a short-circuit merge), the
mux's slice args are fresh and the dispatch forwards them into the entries' phis,
which the merge-phi machinery then resolves."""
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
# Values the dispatch forwards to entry `e`. Empty under `absorb` (the entry has
# no args; its body reads the mux's carries directly). `live` is the set of mux
# arg positions that some redirected edge assigned a real (non-`Undef`) value; a
# position absent from `live` is forwarded as `Undef` — its mux phi would be empty
# (e.g. a value only the body defines, never the skipped continuation entry).
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
not yet redirect edges or dispatch — see [`redirect_edge!`](@ref)/[`dispatch!`](@ref)."""
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

    mux_id = add_block!(m, MBlock(copy(arg_ids), MStmt[], MReturn(), _NOLOC, Any))
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
            nxt = add_block!(m, MBlock(Int[], MStmt[], MReturn(), _NOLOC, Any))
            m.blocks[cur].term = MCondBr(SSAValue(cmp), t_edge, MEdge(nxt, Any[]))
            cur = nxt
        else
            last = targets[end]
            m.blocks[cur].term = MCondBr(SSAValue(cmp), t_edge, MEdge(last, slice_vals(mux, last, live)))
        end
    end
end

# Mux arg positions that some incoming (redirected) edge assigned a real value.
# A position never assigned is "dead" — its phi would be empty; the dispatch
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
targets, then emit the dispatch — MLIR's `createSingleEntryBlock`. Returns the
mux. `extra` supplies (type, per-edge-value-fn) for an extra carried arg (the
latch's `shouldRepeat`); `excluded` entries are left out of the dispatch."""
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
 normalize_cf — the mutate-then-lift driver.

 Repeatedly find one multi-entry situation and collapse it to single-entry with
 an EdgeMultiplexer, until none remain. The lift (`structurize_region!`) then
 only ever sees single-entry regions. Currently handles irreducible (multi-entry)
 loop headers; continuation muxing is added in a later milestone.
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
single entry with a mux, MLIR's `createSingleEntryBlock` over entry∪back edges.
Returns `true` if it muxed one, `false` if the CFG has no irreducible SCC."""
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

    # Deterministic pick (no block-index leak into structure beyond a stable
    # tie-break): smallest SCC id, entry blocks sorted (I1 / D74999).
    S = by_scc[minimum(keys(by_scc))]
    Sset = Set(S)
    entry_blocks = sort!([b for b in S if any(p -> p ∉ Sset, cfg.blocks[b].preds)])
    @assert length(entry_blocks) >= 1 "irreducible SCC with no entry block"

    # Separate the edges into entry blocks: external (entry edges) and in-SCC
    # (back edges). Both route through the entry mux; the back edges are routed a
    # second time through a latch so the header gets a single back edge.
    entry_refs = EdgeRef[]
    back_refs = EdgeRef[]
    for src in sort!(collect(1:nb)), e in entry_blocks
        dst = src in Sset ? back_refs : entry_refs
        append!(dst, edge_refs(m, src, e))
    end

    # 1. Entry mux: collapse the multiple entry blocks to one header. It *absorbs*
    #    the entries' args (becomes the loop header carrying them); each entry, a
    #    dispatch arm reached only from the mux, reads them directly.
    mux = single_entry_mux!(m, vcat(entry_refs, back_refs); absorb=true)

    # 2. Single back edge: the header now has several back-edge predecessors, each
    #    carrying different header-arg values — which the lift's single carried-
    #    value set can't represent. Route the back edges through a latch (a mux
    #    onto the single target = the header), unifying them into one back edge.
    if length(back_refs) >= 2
        single_entry_mux!(m, back_refs)        # target = the header mux; absorb=false
    end
    return true
end

# M4 SPIKE: single-exiting latch ----------------------------------------------

"""Natural loops on the MBlock CFG: header id → set of in-loop block ids. A back
edge is `src→header` where `header` dominates `src`."""
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

"""Route a loop's back edges and exit edges through one latch — MLIR's
`createSingleExitingLatch`. Back edges carry `shouldRepeat=1`, exit edges `=0`;
the latch branches on `shouldRepeat` back to `header` (the single back edge) or
to a fresh exit-dispatch block that switches to the original exit targets (the
single exit edge). The loop is then single-back-edge / single-exit-edge."""
function single_exiting_latch!(m::MCFG, header::Int,
                               back_refs::Vector{EdgeRef}, exit_refs::Vector{EdgeRef})
    exit_targets = Int[]
    for r in exit_refs
        t = edge_of(m, r).target
        t in exit_targets || push!(exit_targets, t)
    end
    targets = vcat([header], exit_targets)          # header first → entry_index 0

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
    exitblk = add_block!(m, MBlock(Int[], MStmt[], MReturn(), _NOLOC, Any))
    m.blocks[latch].term = MCondBr(SSAValue(cmp), header_edge, MEdge(exitblk, Any[]))

    if isempty(exit_targets)
        m.blocks[exitblk].term = MReturn()           # infinite loop: unreachable
    else
        dispatch!(m, mux; excluded=Set{Int}([header]), live, from=exitblk)
    end
    return mux
end

"""Find one natural loop with ≥2 exit edges (the multi-exit shape the lift's
`find_loop_exit` heuristic mishandles) and collapse it to a single-exiting latch.
Returns `true` if it transformed one. SPIKE: trigger is `≥2 exit edges`."""
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
        length(exit_refs) >= 2 || continue
        single_exiting_latch!(m, h, back_refs, exit_refs)
        return true
    end
    return false
end

"""Mutate `m` until no multi-entry situation remains. Each mux strictly reduces
the count (the mux block is single-entry by construction), so this terminates."""
function normalize_cf!(m::MCFG)
    changed = false
    guard = 0
    limit = length(m.blocks) + 16
    while normalize_one_irreducible!(m) ||
          (get(ENV, "IRS_M4", "0") == "1" && normalize_one_loop_latch!(m))
        changed = true
        guard += 1
        guard > 4 * limit && error("normalize_cf! failed to converge (likely a mux bug)")
    end
    return changed
end

"""
    normalize_cf(ir::IRCode) -> IRCode

Collapse every multi-entry CFG situation (irreducible loop headers; later,
multi-predecessor continuations) to single-entry via edge multiplexers, so the
lift only structurizes single-entry regions. Returns `ir` unchanged when it is
already reducible/single-entry everywhere (the common case) — no perturbation.
"""
function normalize_cf(ir::IRCode)
    # Phase 1: irreducible (multi-entry) loop headers — MBlock-native mutation.
    m = ingest(ir)
    normalize_cf!(m) && (ir = emit(m))
    # Phase 2: multi-predecessor branch continuations (short-circuits, nested
    # gated bodies) — reuses the lift's branch_continuation on the (now reducible)
    # IRCode.
    return normalize_continuations(ir)
end

#=============================================================================
 Continuation multiplexer.

 A conditional whose two arms reconverge at MORE THAN ONE block (the short-circuit
 shape `if a||b { body }`: `body` is reached from both arms, and so is the merge)
 has a multi-entry continuation. Route every edge into that continuation through
 one mux so the continuation becomes single-entry; the lift then structurizes it
 with the ordinary IfOp path (no shape-matching). This reuses the lift's own
 `branch_continuation` exclusion analysis (loop-aware), run on the current IRCode.
=============================================================================#

# The two successors of a conditional block: false = GotoIfNot.dest, true = the
# other CFG successor (mirrors emit_branch!).
function _condbr_dests(ir::IRCode, E::Int)
    g = find_terminator(ir, E)::GotoIfNot
    false_dest = g.dest
    succs = ir.cfg.blocks[E].succs
    true_dest = length(succs) == 1 ? only(succs) : first(s for s in succs if s != false_dest)
    return true_dest, false_dest
end

# Minimal LoopCtx for the innermost loop enclosing `E` — `branch_continuation`
# uses only `header`/`loop_blocks` (to skip the loop's back edge and exit edges,
# which are not part of a branch's forward continuation).
function _enclosing_loop_ctx(ctx::StructurizeCtx, E::Int)
    best_h = 0; best_body = nothing; best_size = typemax(Int)
    for (h, body) in ctx.loop_map
        if E in body && length(body) < best_size
            best_h = h; best_body = body; best_size = length(body)
        end
    end
    best_body === nothing && return nothing
    return LoopCtx(best_h, best_body, IRValue[], IRValue[], nothing)
end

# Find one conditional with a multi-entry continuation; return (E, entries) or
# nothing. `entries` are the distinct continuation blocks (>1).
function _find_multientry_continuation(ctx::StructurizeCtx)
    ir = ctx.ir
    all_blocks = Set(1:length(ir.cfg.blocks))
    for E in 1:length(ir.cfg.blocks)
        find_terminator(ir, E) isa GotoIfNot || continue
        lctx = _enclosing_loop_ctx(ctx, E)
        true_dest, false_dest = _condbr_dests(ir, E)
        then_blocks, else_blocks, _ =
            find_branch_regions(ctx, E, true_dest, false_dest, all_blocks, lctx)
        entries, notcont = branch_continuation(ctx, E, true_dest, false_dest,
                                               then_blocks, else_blocks, all_blocks, lctx)
        length(entries) > 1 && return (E, entries, notcont)
    end
    return nothing
end

"""
    normalize_continuations(ir::IRCode) -> IRCode

Collapse every multi-predecessor branch continuation to single-entry with an edge
multiplexer (MLIR `createSingleEntryBlock` for the continuation), to a fixpoint.
Returns `ir` unchanged when no conditional has a multi-entry continuation. After
this, `find_branch_regions` always finds a singleton merge, so the lift's ordinary
IfOp path handles short-circuits, N-way merges, and nested gated bodies uniformly.
"""
function normalize_continuations(ir::IRCode)
    guard = 0
    while true
        ctx = StructurizeCtx(ir)
        found = _find_multientry_continuation(ctx)
        found === nothing && return ir
        E, entries, notcont = found

        # The continuation edges: every edge from a branch-region block (notcont)
        # into a continuation entry. Routing them through one mux makes the
        # continuation single-entry. Entries keep their phis (a merge may also be
        # reached from inside the continuation), so absorb=false.
        entryset = Set(entries)
        refs = EdgeRef[]
        m = ingest(ir)
        for b in notcont, succ in ir.cfg.blocks[b].succs
            succ in entryset && append!(refs, edge_refs(m, b, succ))
        end
        single_entry_mux!(m, refs)
        ir = emit(m)

        guard += 1
        guard > length(ir.cfg.blocks) + 64 &&
            error("normalize_continuations failed to converge (likely a mux bug)")
    end
end
