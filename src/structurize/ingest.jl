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
                mb.term_id = si
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
            # The terminator (e.g. a `GotoIfNot`) is not a body statement, but it
            # carries the source location for the lifted control-flow op (IfOp,
            # YieldOp, …). Anchor it at its own PC so the op resolves a location
            # even when the block has no body (e.g. `if arg`).
            if b.term_id != 0 && b.term_codeloc[1] != 0
                setloc!(b.term_id, b.term_codeloc); line_map[b.term_id] = -b.term_id
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
            if b.term_id != 0
                li = Int(b.term_codeloc[1]); li != 0 && (line_map[b.term_id] = -li)
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

