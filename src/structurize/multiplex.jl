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

"""Type of any value reference (for undef-fill / arg typing)."""
function id_type(m::MCFG, id::Int)
    haskey(m.types, id) && return m.types[id]
    # body statement?
    for b in m.blocks, s in b.body
        s.id == id && return s.type
    end
    return Any
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
    di = ir.debuginfo
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

"""
    emit(m::MCFG) -> IRCode

Rebuild a dense `IRCode` from the mutable form. Chooses a fallthrough-preserving
block order (inserting trampolines as needed), reconstructs phi nodes from block
arguments + per-edge operands, remaps stable ids to dense positions, and rebuilds
the CFG and debug info. Mutates `m` (appends trampolines); emit once per `MCFG`.
"""
function emit(m::MCFG)
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
    cfg_index = Int[]
    for r in bb_ranges
        push!(bb_blocks, BasicBlock(StmtRange(first(r), last(r)), Int[], Int[]))
        push!(cfg_index, first(r))
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
