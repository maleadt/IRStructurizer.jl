# The edge multiplexer (port of MLIR CFGToSCF's EdgeMultiplexer).
#
# The structurizer lifts only single-entry regions. To reach that shape for the
# hard cases (irreducible multi-entry loop headers and multi-predecessor branch
# continuations, i.e. short-circuits) the CFG is mutated so every such region
# becomes single-entry, then the ordinary lift runs on the result. The mechanism:
# insert a single multiplexer block, redirect all incoming edges through it, and
# dispatch from it by an integer discriminator.
#
# Work happens on the mutable, explicit-edge block form (`MBlock`) carrying stable
# ids. Block arguments and per-edge operands replace SSA phi nodes, so redirecting
# an edge is local.
#
# The mux's N-way dispatch is emitted as a GotoIfNot compare-chain on the
# discriminator, since Julia IR has no switch. The mutated CFG is ordinary
# reducible IR that the existing lift handles with no new concepts; for N=2 the
# chain is a single GotoIfNot, lifting to one IfOp.
#
# Types live in `structurize/mcfg.jl`; `ingest` (the IRCode boundary) in
# `structurize/ingest.jl`; CFG analysis and the normalization driver in
# `structurize/normalize.jl`.

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

