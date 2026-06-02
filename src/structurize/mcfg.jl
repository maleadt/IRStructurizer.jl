# The explicit-edge mutable CFG (`MBlock`/`MCFG`) — MLIR's block-argument /
# per-edge-operand IR shape, the single working form for the whole structurizer.
#
# Julia's `IRCode` is dense (SSA value == position) and fallthrough-sensitive
# (`GotoIfNot` falls through to the next block on `true`), so it cannot be mutated
# in place. The `MCFG` carries *stable ids* through CFG mutation (irreducible /
# multi-exit-loop / continuation normalization, see `multiplex.jl`) and is then
# lifted to the structured IR directly — block arguments + per-edge operands stand
# in for SSA phi nodes, so redirecting an edge is local. `ingest` (IRCode → MCFG)
# is the only conversion in the production pipeline; the lift reads this form.
#
# These type definitions live here (rather than in `multiplex.jl`) so the lift's
# `StructurizeCtx` and the walk's `::MReturn`/`::MCondBr` method signatures, which
# are defined before `multiplex.jl` is included, can name the types.

"""An edge to a target block, carrying the operands for the target's block
arguments (one per arg, in order). Operands are `SSAValue`/`Argument`/constant/
`Undef`. `Undef` marks an unassigned phi slot (a dead/undef predecessor path)."""
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
end
MBlock() = MBlock(Int[], MStmt[], MReturn(), (Int32(0), Int32(0), Int32(0)))

"""The whole mutable CFG. Blocks are indexed by id == position in `blocks`; the
vector only ever grows (mux/trampoline blocks appended), so ids are stable.
`types`/`codelocs` cover block-argument and synthesized ids; body-statement
types/codelocs live in the `MStmt`s."""
mutable struct MCFG
    blocks::Vector{MBlock}
    entry::Int
    types::Dict{Int, Any}              # id → type (block args + synthesized stmts)
    codelocs::Dict{Int, NTuple{3, Int32}}  # id → codeloc (block args + synthesized)
    next_id::Int                       # next fresh stable id
    # carried through to the lift / SCI
    argtypes::Vector{Any}
    sptypes::Vector{Any}
    debuginfo::Any
    valid_worlds::Any
end

alloc_id!(m::MCFG) = (id = m.next_id; m.next_id += 1; id)

"""Append a new block, returning its id (== its position; the vector only grows)."""
function add_block!(m::MCFG, b::MBlock)
    push!(m.blocks, b)
    return length(m.blocks)
end
