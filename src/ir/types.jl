# structured IR definitions

export StructuredIRCode, Undef, Instruction, instructions, arguments, value_type,
       insert_before!, insert_after!, terminator, terminator!, operands,
       source_location

#=============================================================================
 Block Arguments (for loop carried values)
=============================================================================#

"""
    BlockArgument

Represents a block argument (similar to MLIR block arguments).
Used for loop carried values and condition branch results.
"""
struct BlockArgument
    id::Int
    type::Any  # Julia type
end

#=============================================================================
 Undef - placeholder for structurization artifacts
=============================================================================#

"""
    Undef

Typed undefined value, analogous to LLVM's `undef`/`poison` or SPIR-V's `OpUndef`.

Inserted during structurization when a phi node has a missing predecessor edge.
In a structured IfOp, both branches must yield equal arity, but the original IR
may only define a value on one path. The dead path gets `Undef(T)`. This value
is never observed at runtime (guarded by the branch condition).
"""
struct Undef
    type::Any  # Julia type
end

Base.show(io::IO, u::Undef) = print(io, "undef::$(u.type)")

#=============================================================================
 IR Values - references to SSA values or block arguments
=============================================================================#

# IRValue: Values used in structured IR
# - SSAValue, Argument, SlotNumber: references to Julia IR values
# - BlockArgument: block arguments for control flow
# - Undef: structurization artifact for dead branches
# - Raw values (Integer, Float, etc.): compile-time constants
const IRValue = Any

#=============================================================================
 SSAMap - ordered map from SSA index to (stmt, type)
=============================================================================#

"""
    SSAMap <: AbstractDict{Int, NamedTuple{(:stmt, :type, :flag)}}

An ordered map from SSA indices to `(; stmt, type, flag)` entries.
Used to store block body contents with their original Julia SSA indices.

`flag` is the per-statement `IR_FLAG_*` bitmask carried over from
`IRCode.stmts.flag` at structurization (see `Compiler/src/optimize.jl`),
or `0` (`IR_FLAG_NULL`) for statements synthesized after structurization.

Indexing by SSA index: `m[ssa_idx]` returns `(; stmt, type, flag)` or throws `KeyError`,
`get(m, ssa_idx, default)` returns `default` if missing. `setindex!` accepts any
NamedTuple subset of `(stmt, type, flag)`; fields not mentioned are preserved.
Iteration yields `idx => (; stmt, type, flag)` pairs.

Storage is parallel `Vector`s (analogous to `Core.Compiler.InstructionStream`
in `Compiler/src/ssair/ir.jl`), with a side `pos_by_idx::Dict{Int,Int}`
giving O(1) lookup from SSA index to vector position.
"""
struct SSAMap <: AbstractDict{Int, @NamedTuple{stmt::Any, type::Any, flag::UInt32}}
    ssa_idxes::Vector{Int}
    stmts::Vector{Any}
    types::Vector{Any}
    flags::Vector{UInt32}  # IR_FLAG_* bitmask per stmt, parallel to stmts/types
    pos_by_idx::Dict{Int, Int}  # ssa_idx to position in the parallel vectors
end

SSAMap() = SSAMap(Int[], Any[], Any[], UInt32[], Dict{Int,Int}())

# Iteration yields idx => (; stmt, type, flag) pairs.
@inline function Base.iterate(m::SSAMap, state::Int=1)
    state > length(m.ssa_idxes) && return nothing
    idx = m.ssa_idxes[state]
    entry = (; stmt=m.stmts[state], type=m.types[state], flag=m.flags[state])
    return Pair(idx, entry), state + 1
end

Base.length(m::SSAMap) = length(m.ssa_idxes)
Base.haskey(m::SSAMap, ssa_idx::Int) = haskey(m.pos_by_idx, ssa_idx)

# Lookup by SSA index
function Base.getindex(m::SSAMap, ssa_idx::Int)
    i = get(m.pos_by_idx, ssa_idx, 0)
    i == 0 && throw(KeyError(ssa_idx))
    return (; stmt=m.stmts[i], type=m.types[i], flag=m.flags[i])
end

function Base.get(m::SSAMap, ssa_idx::Int, default)
    i = get(m.pos_by_idx, ssa_idx, 0)
    i == 0 && return default
    return (; stmt=m.stmts[i], type=m.types[i], flag=m.flags[i])
end

# Push raw tuple. The 3-tuple form defaults the flag to IR_FLAG_NULL (0), used by
# passes that synthesize new statements without an inferred flag. The 4-tuple form
# takes an explicit flag and is used by the IRCode ingestion site and by sites that
# relocate an existing stmt and want to preserve its flag.
function Base.push!(m::SSAMap, (idx, stmt, type)::Tuple{Int,Any,Any})
    push!(m, (idx, stmt, type, UInt32(0)))
end

function Base.push!(m::SSAMap, (idx, stmt, type, flag)::Tuple{Int,Any,Any,UInt32})
    push!(m.ssa_idxes, idx)
    push!(m.stmts, stmt)
    push!(m.types, type)
    push!(m.flags, flag)
    m.pos_by_idx[idx] = length(m.ssa_idxes)
    return nothing
end

# Lazy iterators (keys(m)/values(m) also available via AbstractDict)
indices(m::SSAMap) = (idx for idx in m.ssa_idxes)
statements(m::SSAMap) = (stmt for stmt in m.stmts)
types(m::SSAMap) = (typ for typ in m.types)
flags(m::SSAMap) = (f for f in m.flags)

# Mutation: setindex! accepts any NamedTuple subset of (stmt, type, flag).
# Fields not mentioned are preserved: `m[idx] = (type=Float64,)` overwrites
# only the type, keeping stmt and flag.
function Base.setindex!(m::SSAMap, entry::NamedTuple{names}, ssa_idx::Int) where {names}
    names ⊆ (:stmt, :type, :flag) ||
        throw(ArgumentError("SSAMap entry keys must be a subset of (:stmt, :type, :flag), got $names"))
    i = get(m.pos_by_idx, ssa_idx, 0)
    i == 0 && throw(KeyError(ssa_idx))
    haskey(entry, :stmt) && (m.stmts[i] = entry.stmt)
    haskey(entry, :type) && (m.types[i] = entry.type)
    haskey(entry, :flag) && (m.flags[i] = entry.flag)
    return entry
end

# Mutation: delete! for removing a statement
function Base.delete!(m::SSAMap, ssa_idx::Int)
    i = get(m.pos_by_idx, ssa_idx, 0)
    i == 0 && throw(KeyError(ssa_idx))
    deleteat!(m.ssa_idxes, i)
    deleteat!(m.stmts, i)
    deleteat!(m.types, i)
    deleteat!(m.flags, i)
    delete!(m.pos_by_idx, ssa_idx)
    # Positions after `i` have shifted down by one.
    for j in i:length(m.ssa_idxes)
        m.pos_by_idx[m.ssa_idxes[j]] = j
    end
    return m
end

#=============================================================================
 Terminator Operations
=============================================================================#

"""
    YieldOp

Yields values from a structured control flow region (if/loop body).
The yielded values become the results of the containing IfOp/LoopOp.
"""
struct YieldOp
    values::Vector{IRValue}
end

YieldOp() = YieldOp(IRValue[])

"""
    ContinueOp

Continue to the next iteration of a loop with updated carried values.
"""
struct ContinueOp
    values::Vector{IRValue}
end

ContinueOp() = ContinueOp(IRValue[])

"""
    BreakOp

Break out of a loop, yielding values.
"""
struct BreakOp
    values::Vector{IRValue}
end

BreakOp() = BreakOp(IRValue[])

"""
    ConditionOp

Terminator for the 'before' region of a WhileOp (MLIR scf.condition).
If condition is true, args are passed to the 'after' region.
If condition is false, args become the final loop results.
"""
struct ConditionOp
    condition::IRValue           # Boolean condition
    args::Vector{IRValue}        # Values passed to after region or used as break results
end

ConditionOp(cond::IRValue) = ConditionOp(cond, IRValue[])

const Terminator = Union{ReturnNode, YieldOp, ContinueOp, BreakOp, ConditionOp, Nothing}

"""
    operands(term) -> Vector{IRValue}

Get the carried-value operands of a terminator. Provides uniform access
regardless of whether the terminator stores them in `.values` or `.args`.
"""
operands(t::Union{ContinueOp, BreakOp, YieldOp}) = t.values
operands(t::ConditionOp) = t.args

#=============================================================================
 Abstract Control Flow Type
=============================================================================#

# operands() for ControlFlowOps is defined after the types (below).

"""
    ControlFlowOp

Abstract type for all structured control flow operations.
"""
abstract type ControlFlowOp end

#=============================================================================
 Block (defined before control flow ops so they can reference it)
=============================================================================#

"""
    Block

A block of statements with block arguments and a terminator.
Body is an SSAMap mapping SSA indices to (; stmt, type, flag) entries.
"""
mutable struct Block
    args::Vector{BlockArgument}
    body::SSAMap
    terminator::Terminator
    parent::Any  # containing Block, or StructuredIRCode for entry block, or nothing
end

Block() = Block(BlockArgument[], SSAMap(), nothing, nothing)

"""
    empty!(block::Block)

Remove all instructions from the block body, preserving args, terminator, and parent.
"""
function Base.empty!(block::Block)
    block.body = SSAMap()
    return block
end

"""
    push!(block::Block, idx::Int, stmt, type, [flag])

Push a statement or control flow op to a block with its SSA index, type, and
optional `IR_FLAG_*` bitmask (defaults to 0 / `IR_FLAG_NULL`).
"""
function Base.push!(block::Block, idx::Int, @nospecialize(stmt), @nospecialize(type),
                    flag::UInt32=UInt32(0))
    push!(block.body, (idx, stmt, type, flag))
    # Set parent on sub-blocks when a CF op is inserted (like LLVM's addNodeToList)
    if stmt isa ControlFlowOp
        for b in blocks(stmt)
            b.parent = block
        end
    end
end

"""
    in(val, block::Block) -> Bool
    val ∈ block -> Bool

Determine whether a value is defined in this block (not in ancestors or descendants).
Returns `true` for `SSAValue`s present in the block body and `BlockArgument`s listed
in the block args. Constants, `Argument`s, and other value types return `false`.
"""
Base.in(val::SSAValue, block::Block) = haskey(block.body, val.id)
Base.in(val::BlockArgument, block::Block) = val in block.args
Base.in(@nospecialize(_), ::Block) = false

function Base.show(io::IO, block::Block)
    print(io, "Block(")
    if !isempty(block.args)
        print(io, "args=", length(block.args), ", ")
    end
    n_ops = count(p -> last(p).stmt isa ControlFlowOp, block.body)
    n_exprs = length(block.body) - n_ops
    print(io, n_exprs + n_ops, " items")
    print(io, ")")
end

# Iteration protocol for Block - delegates to SSAMap, yielding idx => (; stmt, type, flag)
Base.iterate(block::Block) = iterate(block.body)
Base.iterate(block::Block, state) = iterate(block.body, state)
Base.length(block::Block) = length(block.body)
Base.eltype(::Type{Block}) = eltype(SSAMap)

#=============================================================================
 Instruction - handle into an SSAMap entry
=============================================================================#

"""
    Instruction

A handle into an SSAMap entry: an SSA index paired with the containing
`Block`. Field reads/writes go through the live `Block.body` entry, so a
handle held across mutations always sees the current `(stmt, type, flag)`.

Yielded by `instructions(block)` and usable as a key in `UseIndex`.

Field access is Symbol-keyed: `inst[:stmt]`, `inst[:type]`, `inst[:flag]`
read the live entry, and `inst[:stmt] = ...` etc. write back. The containing
block is `inst.block`, the SSA index is `inst.ssa_idx`. The polymorphic
`value_type(inst)` is a convenience for `inst[:type]` and also accepts
non-Instruction values (`SSAValue`, `BlockArgument`).

Analogous to `Core.Compiler.Instruction` in `Compiler/src/ssair/ir.jl`,
which is also a `(storage, key)` handle dispatching to parallel field
vectors via `node[:stmt]` etc., except that the storage here is keyed by
SSA index (preserved across structurization) rather than by dense position.
Becomes stale on `delete!` of the underlying entry. Identity (`==`, `hash`)
is by `ssa_idx` only, which is sound because SSA indices are globally unique
within a `StructuredIRCode` and never reused after `delete!` (allocated via
`max_ssa_idx`, enforced by `validate_ssa_uniqueness`).
"""
struct Instruction
    ssa_idx::Int
    block::Block
end

"""Get the Julia type of the instruction result."""
value_type(i::Instruction) = i[:type]

"""Convert to SSAValue for use in operand positions."""
Core.SSAValue(i::Instruction) = SSAValue(i.ssa_idx)

Base.:(==)(a::Instruction, b::Instruction) = a.ssa_idx == b.ssa_idx
Base.hash(i::Instruction, h::UInt) = hash(i.ssa_idx, h)

function Base.show(io::IO, i::Instruction)
    print(io, "Instruction(%$(i.ssa_idx)")
    s = i[:stmt]
    if s isa ControlFlowOp
        print(io, " = ", typeof(s))
    elseif s isa Expr
        print(io, " = ", s.head, "(...)")
    end
    print(io, ")")
end

#=============================================================================
 Block accessors (LLVM.jl-style)
=============================================================================#

"""
    instructions(block::Block)

Iterate over the instructions in a block, yielding `Instruction` objects.
Each `Instruction` bundles the SSA index, statement, and type, so users never
need to interact with SSAMap directly.

Analogous to LLVM.jl's `instructions(bb::BasicBlock)`.
"""
instructions(b::Block) = InstructionIterator(b)

struct InstructionIterator
    block::Block
end

Base.length(it::InstructionIterator) = length(it.block.body)
Base.eltype(::Type{InstructionIterator}) = Instruction

function Base.iterate(it::InstructionIterator, state::Int=1)
    m = it.block.body
    state > length(m.ssa_idxes) && return nothing
    return Instruction(m.ssa_idxes[state], it.block), state + 1
end

"""
    arguments(block::Block) -> Vector{BlockArgument}

Get the block arguments. Analogous to LLVM.jl's `parameters(f)`.
"""
arguments(block::Block) = block.args

"""
    terminator(block::Block) -> Terminator

Get the block's terminator. Analogous to LLVM's `getTerminator()`.
"""
terminator(block::Block) = block.terminator

"""
    terminator!(block::Block, term) -> term

Set the block's terminator.
"""
terminator!(block::Block, term) = (block.terminator = term; term)

"""
    isempty(block::Block) -> Bool

Check whether a block has no instructions (terminator not counted).
"""
Base.isempty(block::Block) = isempty(block.body.ssa_idxes)

#=============================================================================
 Control Flow Types
=============================================================================#

"""
    IfOp

Structured if-then-else operation.
"""
mutable struct IfOp <: ControlFlowOp
    condition::IRValue
    then_region::Block
    else_region::Block
end

function Base.show(io::IO, ::IfOp)
    print(io, "IfOp()")
end

"""
    ForOp(lower, upper, step, iv_arg, body, init_values; inclusive=false)

Counted loop over an integer range. The induction variable `iv_arg` takes the
values `lower + j*step` for `j = 0, 1, ...`; `upper` bounds them, inclusively when
`inclusive` is set and exclusively otherwise. The flag describes endpoint
membership only, not where the source loop tested its condition.

# Counted-range contract

The op describes a finite, monotonic, non-wrapping iteration; wraparound is not
part of its contract. In mathematical terms (no arithmetic in the IV type):

| form      | empty when       | visited values                       | requirement (nonempty ranges)                  |
|-----------|------------------|--------------------------------------|------------------------------------------------|
| inclusive | `lower > upper`  | `lower + j*step`, ending at `upper`  | `upper - lower` is a multiple of `step`        |
| exclusive | `lower >= upper` | `lower + j*step < upper`             | the first increment reaching or crossing `upper` is representable in the IV type |

- The IV, `lower`, `upper` and `step` share one concrete `Base.BitInteger` type
  (`Core.Const` widened). Ordering is that type's own: signed or unsigned
  comparisons follow the IV type. Other types are refused.
- `step` is strictly positive. Descending loops use the general ops.
- `lower`, `upper` and `step` are loop-invariant and defined before the op.
- An inclusive `upper` is the last visited value itself; the lowering stops on
  equality with it and never computes `upper + step`, so a range ending at
  `typemax` of its type is exact. An exclusive range uses an ordinary header test
  and increment, which its representability requirement keeps from wrapping.

# Results and body

`init_values` are the initial loop-carried values; `body.args` are the carries
(the IV is `iv_arg`, not a body arg); the body's `ContinueOp` supplies the next
carried values, in the same order and count. The op's results are the final
carried values, or the initial ones for an empty range. The result tuple may
expose only a prefix of the carries; trailing invariant carries need no result
slot. The IV is not a result:
a producer that needs the escaping IV keeps it as an explicit carry (whose final
value can differ from `upper`, e.g. the post-increment IV of a `while` loop, or
the init of an empty loop). Extra exit values (loop-internal values used after
the loop) ride as carries with `Undef` initial values. The body owns no `BreakOp`:
a loop with a secondary exit stays a `LoopOp`.

# Producer and consumer obligations

Structural validation (`validate_terminators`) checks the IV type, arities, the
absence of breaks, and statically contradictory constant bounds/steps. Dynamic
legality is the producer's obligation: `promote_loops!` builds a `ForOp` only
after proving the contract from the source loop (see `promote.jl`), and an
external constructor takes on the same proof. Consumers may lower the op to a
target's counted loop only when that target's extra requirements hold, and can
otherwise use [`expand_for_loops!`](@ref), the exact expansion into `IfOp`,
`LoopOp` and `WhileOp`.
"""
mutable struct ForOp <: ControlFlowOp
    lower::IRValue
    upper::IRValue
    step::IRValue
    iv_arg::BlockArgument
    body::Block
    init_values::Vector{IRValue}
    inclusive::Bool
end
ForOp(lower, upper, step, iv_arg::BlockArgument, body::Block, init_values;
      inclusive::Bool=false) =
    ForOp(lower, upper, step, iv_arg, body, init_values, inclusive)

"""The integer type a `ForOp` counts with: `T` widened from a `Core.Const`, if it
is a concrete `Base.BitInteger`, else `nothing`. Bounds are compared signed or
unsigned by this type (`forop_iv_signed`)."""
function forop_iv_type(@nospecialize(T))
    T = widenconst(T)
    return T isa DataType && T <: Base.BitInteger ? T : nothing
end
forop_iv_signed(T::DataType) = T <: Signed

function Base.show(io::IO, op::ForOp)
    print(io, "ForOp(")
    if !isempty(op.init_values)
        print(io, "init_values=", length(op.init_values))
    end
    print(io, ")")
end

"""
    WhileOp

MLIR-style while loop with before (condition) and after (body) regions.
init_values = initial values for loop-carried variables.
"""
mutable struct WhileOp <: ControlFlowOp
    before::Block
    after::Block
    init_values::Vector{IRValue}
end

function Base.show(io::IO, op::WhileOp)
    print(io, "WhileOp(")
    if !isempty(op.init_values)
        print(io, "init_values=", length(op.init_values))
    end
    print(io, ")")
end

"""
    LoopOp

General loop with dynamic exit via BreakOp/ContinueOp.
init_values = initial values for loop-carried variables.

Arity contract (all equal):
- `init_values`, `body.args`, `ContinueOp.values`, and `BreakOp.values` must have equal length.
- Extra exit values (loop-internal values used after the loop) are included as loop-carried
  variables with `Undef` initial values.
"""
mutable struct LoopOp <: ControlFlowOp
    body::Block
    init_values::Vector{IRValue}
end

function Base.show(io::IO, op::LoopOp)
    print(io, "LoopOp(")
    if !isempty(op.init_values)
        print(io, "init_values=", length(op.init_values))
    end
    print(io, ")")
end

#=============================================================================
 Block iteration
=============================================================================#

export blocks

"""
    blocks(sci::StructuredIRCode)

Get the top-level blocks of the structured IR (just the entry block).
"""
blocks(sci) = (sci.entry,)  # defined fully after StructuredIRCode

"""
    blocks(op::ControlFlowOp)

Get the immediate sub-blocks of a control flow operation.
Non-recursive: returns only one level of nesting.
"""
blocks(op::IfOp) = (op.then_region, op.else_region)
blocks(op::ForOp) = (op.body,)
blocks(op::WhileOp) = (op.before, op.after)
blocks(op::LoopOp) = (op.body,)
blocks(::ControlFlowOp) = ()

"""Recursively fix parent pointers for all sub-blocks."""
function fix_parents!(block::Block)
    for (_, entry) in block.body
        if entry.stmt isa ControlFlowOp
            for b in blocks(entry.stmt)
                b.parent = block
                fix_parents!(b)
            end
        end
    end
end

"""
    operands(op::ControlFlowOp) -> Vector{IRValue}

Get the values flowing into a control flow operation from the parent scope.
For loops, this includes bounds and init values. For IfOp, this is the condition.
"""
operands(op::IfOp)    = Any[op.condition]
operands(op::ForOp)   = Any[op.lower, op.upper, op.step, op.init_values...]
operands(op::WhileOp) = copy(op.init_values)
operands(op::LoopOp)  = copy(op.init_values)

#=============================================================================
 Source Location (debug info)
=============================================================================#

"""
    SourceLocation

A resolved source location entry. An inlining stack is represented as
`Vector{SourceLocation}` ordered `[outermost, ..., innermost]`.
"""
struct SourceLocation
    method::Any   # Method, MethodInstance, or Symbol
    file::Symbol
    line::Int32
end

function Base.show(io::IO, loc::SourceLocation)
    print(io, loc.method, " at ", loc.file, ":", loc.line)
end

#=============================================================================
 StructuredIRCode - the structured IR for a function
=============================================================================#

"""
    StructuredIRCode

Represents a function's code with a structured view of control flow.

The entry Block contains nested control flow ops (IfOp, ForOp, etc.) after
structurization.
"""
mutable struct StructuredIRCode
    const argtypes::Vector{Any}
    const sptypes::Vector{Any}
    entry::Block
    max_ssa_idx::Int
    max_arg_idx::Int
    # Debug info, accessed via source_location().
    # debuginfo_table: the original source table (linetable or DebugInfoStream), or nothing
    # line_map: ssa_idx to val, where val < 0 means direct reference (-val is PC or linetable idx),
    #           val > 0 means anchor (val is another SSA idx to follow). empty!(line_map) wipes all.
    const debuginfo_table::Any
    const line_map::Dict{Int, Int}

    # World-age range over which this IR is consistent. Carried from
    # `IRCode.valid_worlds` at ingest. Anchors binding-partition lookups
    # (see [`global_type`](@ref)) so module-binding type queries return the
    # type the IR was inferred against, even if the world has advanced
    # since. Defaults to the unbounded range for hand-built SCIs (tests,
    # MWEs) and on Julia 1.11 (which lacks `IRCode.valid_worlds`).
    const valid_worlds::WorldRange
end

# Minimal constructor for hand-built SCIs (tests, MWEs). Wires the parent
# chain (entry to SCI, sub-blocks to containing block) so `root(block)`
# walks succeed. The full `StructuredIRCode(ir::IRCode; ...)` constructor
# does the same after structurization.
function StructuredIRCode(argtypes, sptypes, entry, max_ssa_idx)
    sci = StructuredIRCode(argtypes, sptypes, entry, max_ssa_idx, 0, nothing,
                           Dict{Int,Int}(),
                           WorldRange(typemin(UInt), typemax(UInt)))
    sci.entry.parent = sci
    fix_parents!(sci.entry)
    return sci
end

"""
    copy(sci::StructuredIRCode) -> StructuredIRCode

Structural copy: every `Block`, control-flow op, statement map, argument list
and terminator is new, so the copy can be rewritten (statements added, removed
or replaced, carries changed) without touching `sci`. Statements themselves are
shared, as in `Compiler.copy(::IRCode)`; `Expr`s are not deep-copied, which also
keeps `MethodInstance`s of `:invoke`s and `Module`s of `GlobalRef`s out of the
copy. The debug-info table is shared read-only; the line map is copied.
"""
function Base.copy(sci::StructuredIRCode)
    new_sci = StructuredIRCode(
        copy(sci.argtypes), copy(sci.sptypes),
        copy(sci.entry),
        sci.max_ssa_idx, sci.max_arg_idx,
        sci.debuginfo_table,  # shared (read-only)
        copy(sci.line_map),
        sci.valid_worlds,
    )
    new_sci.entry.parent = new_sci
    fix_parents!(new_sci.entry)
    return new_sci
end

function Base.copy(m::SSAMap)
    return SSAMap(copy(m.ssa_idxes), Any[copy_stmt(s) for s in m.stmts], copy(m.types),
                  copy(m.flags), copy(m.pos_by_idx))
end

"""Structural copy of a block (see `copy(::StructuredIRCode)`); the parent is
left unset for the caller to wire (`fix_parents!`)."""
function Base.copy(block::Block)
    return Block(copy(block.args), copy(block.body), copy_terminator(block.terminator), nothing)
end

# Control-flow ops are copied with their blocks; other statements are shared.
copy_stmt(@nospecialize(s)) = s
copy_stmt(op::IfOp) = IfOp(op.condition, copy(op.then_region), copy(op.else_region))
copy_stmt(op::ForOp) = ForOp(op.lower, op.upper, op.step, op.iv_arg, copy(op.body),
                             copy(op.init_values), op.inclusive)
copy_stmt(op::WhileOp) = WhileOp(copy(op.before), copy(op.after), copy(op.init_values))
copy_stmt(op::LoopOp) = LoopOp(copy(op.body), copy(op.init_values))

copy_terminator(t::YieldOp) = YieldOp(copy(t.values))
copy_terminator(t::ContinueOp) = ContinueOp(copy(t.values))
copy_terminator(t::BreakOp) = BreakOp(copy(t.values))
copy_terminator(t::ConditionOp) = ConditionOp(t.condition, copy(t.args))
copy_terminator(@nospecialize(t)) = t   # ReturnNode (immutable) or nothing


"""
    StructuredIRCode(ir::IRCode; structurize=true, validate=true)

Create a StructuredIRCode from Julia IRCode.

By default, converts control flow to structured ops (IfOp, ForOp, etc.) and
validates that no unstructured control flow remains.

# Arguments
- `structurize`: If true (default), convert GotoNode/GotoIfNot to structured ops
- `validate`: If true (default), throw `UnstructuredControlFlowError` if unstructured
  control flow remains after structurization
- `promote`: If true (default), run the `LoopOp` to `WhileOp`/`ForOp` promotion post-pass.
  Pass `false` to keep the generic `LoopOp` form.
"""
function StructuredIRCode(ir::IRCode; structurize::Bool=true, validate::Bool=true,
                          promote::Bool=true)
    # Collapse every multi-entry CFG situation (irreducible loop headers, multi-exit
    # loops, multi-predecessor continuations) to single-entry with edge multiplexers,
    # then lift the resulting `MCFG` (block args + per-edge operands replace phi nodes).
    # `lift_mcfg` captures debug info from the `MBlock` codelocs and runs the
    # structurize walk.
    if structurize && !isempty(ir.stmts.stmt)
        return lift_mcfg(normalize_cf(ir); validate, promote)
    end

    # Flat view (structurize=false, or empty IR): the raw IRCode statements in a
    # single block, no normalization. Negative line_map = direct PC ref.
    argtypes = copy(ir.argtypes)
    sptypes = copy(ir.sptypes)
    @static if VERSION >= v"1.12-"
        valid_worlds = ir.valid_worlds
    else
        valid_worlds = WorldRange(typemin(UInt), typemax(UInt))
    end
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    flags = ir.stmts.flag      # per-statement IR_FLAG_* bitmask (effects, nothrow, etc.)
    n = length(stmts)
    @static if VERSION >= v"1.12-"
        debuginfo_table = ir.debuginfo
        line_map = Dict{Int, Int}()
        for i in 1:n
            line_map[i] = -i              # PC = i (identity mapping)
        end
    else
        debuginfo_table = copy(ir.linetable)
        line_map = Dict{Int, Int}()
        for i in 1:n
            li = Int(ir.stmts.line[i])
            li != 0 && (line_map[i] = -li)  # linetable index
        end
    end
    entry = Block()
    for i in 1:n
        stmt = stmts[i]
        if stmt isa ReturnNode
            entry.terminator = stmt
        else
            push!(entry, i, stmt, types[i], flags[i])
        end
    end
    sci = StructuredIRCode(argtypes, sptypes, entry, n, 0,
                           debuginfo_table, line_map, valid_worlds)
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

#=============================================================================
 source_location: resolve SSA index to inlining stack
=============================================================================#

"""
    source_location(sci::StructuredIRCode, ssa_idx::Int) -> Vector{SourceLocation}
    source_location(sci::StructuredIRCode, inst::Instruction) -> Vector{SourceLocation}

Returns the inlining stack for a statement: `[outermost, ..., innermost]`.
Returns `SourceLocation[]` if no debug info is available.
"""
source_location(sci::StructuredIRCode, inst::Instruction) = source_location(sci, inst.ssa_idx)

"""Resolve line_map entry: follow positive anchors to a negative direct reference.
Returns the direct reference (a positive PC or linetable index), or `nothing` if not found."""
function resolve_line(line_map::Dict{Int, Int}, ssa_idx::Int)
    val = get(line_map, ssa_idx, 0)
    while val > 0
        val = get(line_map, val, 0)
    end
    return val == 0 ? nothing : -val
end

@static if VERSION >= v"1.12-"

function source_location(sci::StructuredIRCode, ssa_idx::Int)
    pc = resolve_line(sci.line_map, ssa_idx)
    pc === nothing && return SourceLocation[]
    debuginfo = sci.debuginfo_table::CC.DebugInfoStream
    return resolve_debuginfo(debuginfo, debuginfo.def, pc)
end

function resolve_debuginfo(debuginfo, @nospecialize(def), pc::Int)
    scopes = SourceLocation[]
    append_scopes!(scopes, pc, debuginfo, def) || empty!(scopes)
    return scopes
end

@static if VERSION >= v"1.14-"

# Mirrors Compiler/src/ssair/show.jl append_scopes! for SourceLocation.
function append_scopes!(scopes::Vector{SourceLocation}, pc::Int, debuginfo, @nospecialize(def))
    doupdate = true
    while debuginfo !== nothing
        debuginfo.def isa Symbol || (def = debuginfo.def)
        if pc <= 0
            return false
        elseif !CC.has_prev_debuginfo(debuginfo, pc)
            line = CC.source_location(debuginfo, pc).line
            line <= 0 && (doupdate = false; line = 0)
            push!(scopes, SourceLocation(def, debuginfo_file(debuginfo), Int32(line)))
        else
            prev_debuginfo, prev_pc = CC.prev_debuginfo(debuginfo, pc)
            doupdate &= append_scopes!(scopes, prev_pc, prev_debuginfo, def)
        end
        def = :var"macro expansion"
        debuginfo, pc = CC.edge_debuginfo(debuginfo, pc)
        doupdate |= debuginfo !== nothing
    end
    return doupdate
end

else

# Mirrors the pre-1.14 Compiler/src/ssair/show.jl append_scopes! implementation.
function append_scopes!(scopes::Vector{SourceLocation}, pc::Int, debuginfo, @nospecialize(def))
    doupdate = true
    while true
        debuginfo.def isa Symbol || (def = debuginfo.def)
        codeloc = CC.getdebugidx(debuginfo, pc)
        line::Int = codeloc[1]
        inl_to::Int = codeloc[2]
        doupdate &= line != 0 || inl_to != 0
        if debuginfo.linetable === nothing || pc <= 0 || line < 0
            line < 0 && (doupdate = false; line = 0)
            push!(scopes, SourceLocation(def, debuginfo_file(debuginfo), Int32(line)))
        else
            doupdate = append_scopes!(scopes, line, debuginfo.linetable::Core.DebugInfo, def) && doupdate
        end
        inl_to == 0 && return doupdate
        def = :var"macro expansion"
        debuginfo = debuginfo.edges[inl_to]
        pc = Int(codeloc[3])
    end
end

end

function debuginfo_file(debuginfo)
    def = debuginfo.def
    if def isa MethodInstance
        def = def.def
    end
    if def isa Method
        def = def.file
    end
    def isa Symbol && return def
    return :var"<unknown>"
end

else # Julia 1.11

function source_location(sci::StructuredIRCode, ssa_idx::Int)
    li = resolve_line(sci.line_map, ssa_idx)
    li === nothing && return SourceLocation[]
    linetable = sci.debuginfo_table::Vector
    stack = SourceLocation[]
    idx = li
    while idx != 0
        entry = linetable[idx]::Core.LineInfoNode
        pushfirst!(stack, SourceLocation(entry.method, entry.file, entry.line))
        idx = Int(entry.inlined_at)
    end
    return stack
end

end # @static if
