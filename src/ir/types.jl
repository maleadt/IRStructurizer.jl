# structured IR definitions

export StructuredIRCode, Undef, Inst, instructions, arguments, value_type, stmt,
       insert_before!, insert_after!, terminator, terminator!, operands

#=============================================================================
 Block Arguments (for loop carried values)
=============================================================================#

"""
    BlockArg

Represents a block argument (similar to MLIR block arguments).
Used for loop carried values and condition branch results.
"""
struct BlockArg
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
# - BlockArg: block arguments for control flow
# - Undef: structurization artifact for dead branches
# - Raw values (Integer, Float, etc.): compile-time constants
const IRValue = Any

#=============================================================================
 Inst - instruction bundling SSA index + statement + type
=============================================================================#

"""
    Inst

An instruction in the structured IR, bundling an SSA index with its statement
and type. Analogous to LLVM's `Instruction` which IS a `Value` carrying its type.

Yielded by `instructions(block)`. Can be used as a key in `UseIndex`.
"""
struct Inst
    ssa_idx::Int
    stmt::Any
    typ::Any
end

"""Get the Julia type of the instruction result."""
value_type(i::Inst) = i.typ

"""Get the underlying statement (Expr, ControlFlowOp, etc.)."""
stmt(i::Inst) = i.stmt

"""Convert to SSAValue for use in operand positions."""
Core.SSAValue(i::Inst) = SSAValue(i.ssa_idx)

Base.:(==)(a::Inst, b::Inst) = a.ssa_idx == b.ssa_idx
Base.hash(i::Inst, h::UInt) = hash(i.ssa_idx, h)

function Base.show(io::IO, i::Inst)
    print(io, "Inst(%$(i.ssa_idx)")
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
    args::Vector{BlockArg}
    body::SSAMap
    terminator::Terminator
    parent::Any  # containing Block, or StructuredIRCode for entry block, or nothing
end

Block() = Block(BlockArg[], SSAMap(), nothing, nothing)

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

Iterate over the instructions in a block, yielding `Inst` objects.
Each `Inst` bundles the SSA index, statement, and type — users never
need to interact with SSAMap directly.

Analogous to LLVM.jl's `instructions(bb::BasicBlock)`.
"""
instructions(block::Block) = InstructionIterator(block.body)

struct InstructionIterator
    body::SSAMap
end

Base.length(it::InstructionIterator) = length(it.body)
Base.eltype(::Type{InstructionIterator}) = Inst

function Base.iterate(it::InstructionIterator, state::Int=1)
    m = it.body
    state > length(m.ssa_idxes) && return nothing
    inst = Inst(m.ssa_idxes[state], m.stmts[state], m.types[state])
    return inst, state + 1
end

"""
    arguments(block::Block) -> Vector{BlockArg}

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
    iv_arg::BlockArg
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
end

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

    sci = StructuredIRCode(argtypes, sptypes, entry, n)

    if structurize && n > 0
        ctx = StructurizationContext(types, n + 1)
        ctree = ControlTree(ir)
        sci.entry = control_tree_to_structured_ir(ctree, ir, ctx)
        sci.max_ssa_idx = ctx.next_ssa_idx - 1
    end

    # Entry block's parent is the SCI (sub-blocks get parents via push!)
    sci.entry.parent = sci

    if validate
        validate_scf(sci.entry)
        validate_no_phis(sci.entry)
        validate_terminators(sci)
        validate_ssa_defs(sci)
        validate_ssa_uniqueness(sci)
    end

    return sci
end
