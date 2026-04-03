# structured IR definitions

export StructuredIRCode, Undef, Instruction, instructions, arguments, value_type, stmt, block,
       insert_before!, insert_after!, terminator, terminator!, operands

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
may only define a value on one path. The dead path gets `Undef(T)` — this value
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
 Instruction - convenience view over an SSAMap entry
=============================================================================#

"""
    Instruction

A view over an SSAMap entry, bundling an SSA index with its statement, type,
and containing block. Yielded by `instructions(block)` and usable as a key
in `UseIndex`.

Analogous to MLIR's `Operation` which knows its parent `Block` via `getBlock()`.
"""
struct Instruction
    ssa_idx::Int
    stmt::Any
    typ::Any
    block::Any  # ::Block — untyped to avoid forward reference
end

"""Get the Julia type of the instruction result."""
value_type(i::Instruction) = i.typ

"""Get the underlying statement (Expr, ControlFlowOp, etc.)."""
stmt(i::Instruction) = i.stmt

"""Get the block containing this instruction."""
block(i::Instruction) = i.block

"""Convert to SSAValue for use in operand positions."""
Core.SSAValue(i::Instruction) = SSAValue(i.ssa_idx)

Base.:(==)(a::Instruction, b::Instruction) = a.ssa_idx == b.ssa_idx
Base.hash(i::Instruction, h::UInt) = hash(i.ssa_idx, h)

function Base.show(io::IO, i::Instruction)
    print(io, "Instruction(%$(i.ssa_idx)")
    if i.stmt isa ControlFlowOp
        print(io, " = ", typeof(i.stmt))
    elseif i.stmt isa Expr
        print(io, " = ", i.stmt.head, "(...)")
    end
    print(io, ")")
end

#=============================================================================
 SSAMap - ordered map from SSA index to (stmt, type)
=============================================================================#

"""
    SSAMap <: AbstractDict{Int, NamedTuple{(:stmt, :typ)}}

An ordered map from SSA indices to `(; stmt, typ)` entries.
Used to store block body contents with their original Julia SSA indices.

Indexing by SSA index: `m[ssa_idx]` returns `(; stmt, typ)` or throws `KeyError`,
`get(m, ssa_idx, default)` returns `default` if missing.
Iteration yields `idx => (; stmt, typ)` pairs, enabling `filter(p -> p.second.stmt isa Foo, m)`.

Note: Currently uses linear scan for lookup. If this becomes a bottleneck,
consider switching to `OrderedDict{Int, NamedTuple}` for O(1) access.
"""
struct SSAMap <: AbstractDict{Int, @NamedTuple{stmt::Any, typ::Any}}
    ssa_idxes::Vector{Int}
    stmts::Vector{Any}
    types::Vector{Any}
end

SSAMap() = SSAMap(Int[], Any[], Any[])

# Iteration yields idx => (; stmt, typ) pairs
function Base.iterate(m::SSAMap, state::Int=1)
    state > length(m.ssa_idxes) && return nothing
    idx = m.ssa_idxes[state]
    entry = (; stmt=m.stmts[state], typ=m.types[state])
    return Pair(idx, entry), state + 1
end

Base.length(m::SSAMap) = length(m.ssa_idxes)
Base.haskey(m::SSAMap, ssa_idx::Int) = findfirst(==(ssa_idx), m.ssa_idxes) !== nothing

# Lookup by SSA index
function Base.getindex(m::SSAMap, ssa_idx::Int)
    i = findfirst(==(ssa_idx), m.ssa_idxes)
    i === nothing && throw(KeyError(ssa_idx))
    return (; stmt=m.stmts[i], typ=m.types[i])
end

function Base.get(m::SSAMap, ssa_idx::Int, default)
    i = findfirst(==(ssa_idx), m.ssa_idxes)
    i === nothing && return default
    return (; stmt=m.stmts[i], typ=m.types[i])
end

# Push raw tuple
function Base.push!(m::SSAMap, (idx, stmt, typ)::Tuple{Int,Any,Any})
    push!(m.ssa_idxes, idx)
    push!(m.stmts, stmt)
    push!(m.types, typ)
    return nothing
end

# Lazy iterators (keys(m)/values(m) also available via AbstractDict)
indices(m::SSAMap) = (idx for idx in m.ssa_idxes)
statements(m::SSAMap) = (stmt for stmt in m.stmts)
types(m::SSAMap) = (typ for typ in m.types)

# Mutation: setindex! for replacing a statement in-place
function Base.setindex!(m::SSAMap, entry::NamedTuple{(:stmt, :typ)}, ssa_idx::Int)
    i = findfirst(==(ssa_idx), m.ssa_idxes)
    i === nothing && throw(KeyError(ssa_idx))
    m.stmts[i] = entry.stmt
    m.types[i] = entry.typ
    return entry
end

# Mutation: delete! for removing a statement
function Base.delete!(m::SSAMap, ssa_idx::Int)
    i = findfirst(==(ssa_idx), m.ssa_idxes)
    i === nothing && throw(KeyError(ssa_idx))
    deleteat!(m.ssa_idxes, i)
    deleteat!(m.stmts, i)
    deleteat!(m.types, i)
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

# operands() for ControlFlowOps — defined after the types (below)

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
Body is an SSAMap mapping SSA indices to (stmt, type) entries.
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
    push!(block::Block, idx::Int, stmt, typ)

Push a statement or control flow op to a block with its SSA index and type.
"""
function Base.push!(block::Block, idx::Int, @nospecialize(stmt), @nospecialize(typ))
    push!(block.body, (idx, stmt, typ))
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
    n_ops = count(((_, item, _),) -> item isa ControlFlowOp, block.body)
    n_exprs = length(block.body) - n_ops
    print(io, n_exprs + n_ops, " items")
    print(io, ")")
end

# Iteration protocol for Block - yields (idx, stmt, typ) triples (legacy)
Base.iterate(block::Block) = iterate(block.body)
Base.iterate(block::Block, state) = iterate(block.body, state)
Base.length(block::Block) = length(block.body)
Base.eltype(::Type{Block}) = Tuple{Int,Any,Any}

#=============================================================================
 Block accessors (LLVM.jl-style)
=============================================================================#

"""
    instructions(block::Block)

Iterate over the instructions in a block, yielding `Instruction` objects.
Each `Instruction` bundles the SSA index, statement, and type — users never
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
    inst = Instruction(m.ssa_idxes[state], m.stmts[state], m.types[state], it.block)
    return inst, state + 1
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
    ForOp

Counted for-loop with lower/upper/step bounds.
Iterates while iv < upper (exclusive upper bound).
init_values = initial values for loop-carried variables.

Arity contract (all equal):
- `init_values`, `body.args` (minus IV), and `ContinueOp.values` must have equal length.
- Extra exit values (loop-internal values used after the loop) are included as loop-carried
  variables with `Undef` initial values.
"""
mutable struct ForOp <: ControlFlowOp
    lower::IRValue
    upper::IRValue
    step::IRValue
    iv_arg::BlockArgument
    body::Block
    init_values::Vector{IRValue}
end

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
end

StructuredIRCode(argtypes, sptypes, entry, max_ssa_idx) =
    StructuredIRCode(argtypes, sptypes, entry, max_ssa_idx, 0)

"""
    StructuredIRCode(ir::IRCode; structurize=true, validate=true)

Create a StructuredIRCode from Julia IRCode.

By default, converts control flow to structured ops (IfOp, ForOp, etc.) and
validates that no unstructured control flow remains.

# Arguments
- `structurize`: If true (default), convert GotoNode/GotoIfNot to structured ops
- `validate`: If true (default), throw `UnstructuredControlFlowError` if unstructured
  control flow remains after structurization
"""
function StructuredIRCode(ir::IRCode; structurize::Bool=true, validate::Bool=true)
    argtypes = copy(ir.argtypes)
    sptypes = copy(ir.sptypes)
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    n = length(stmts)

    # Build flat entry block
    entry = Block()
    for i in 1:n
        stmt = stmts[i]
        if stmt isa ReturnNode
            entry.terminator = stmt
        else
            push!(entry, i, stmt, types[i])
        end
    end

    sci = StructuredIRCode(argtypes, sptypes, entry, n, 0)

    if structurize && n > 0
        entry, max_ssa, max_arg = IRStructurizer.structurize(ir)
        max_ssa = rebuildssa!(entry, max_ssa + 1) - 1
        sci.entry = entry
        sci.max_ssa_idx = max_ssa
        sci.max_arg_idx = max_arg
    end

    # Set parent chain: entry → SCI, sub-blocks → containing block.
    # Must be done after structurize+promote since promote_loops! replaces
    # block.body without going through push! (which normally sets parents).
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
