# Utilities for structured IR
#
# Block mutation: parent, root, push!, pushfirst!, insert_before!, insert_after!,
#                 delete!, new_block_arg!
# Statement mutation: block[ssa_idx] = (; stmt, type, flag)  — partial NamedTuple
#                     inst[:stmt] = …, inst[:type] = …, inst[:flag] = …
# Block traversal: eachblock, findblock
# Use tracking: uses(), replace_uses!
# Loop carries: carries()
# Expression inspection: resolve_call, iscall, callee, callargs
# Scope queries: is_defined_outside
# Instruction movement: move_before!, move_after!


#=============================================================================
 Block mutation (SSA-allocating operations)
=============================================================================#

public root, parent, walk_uses!, IndexedUseRef, const_value
export insert_before!, insert_after!, eachblock, findblock,
       new_block_arg!,
       resolve_call, iscall, callee, callargs,
       reachable_terminators, walk, after_arg,
       def, defs,
       is_defined_outside, move_before!, move_after!

"""
    parent(block::Block) -> Union{Block, StructuredIRCode}

Get the immediate parent: the containing block, or the StructuredIRCode for the entry block.
"""
Base.parent(block::Block) = block.parent

"""
    root(block::Block) -> StructuredIRCode

Walk up the parent chain to find the StructuredIRCode root.
"""
function root(block::Block)
    p = block.parent
    while p isa Block
        p = p.parent
    end
    return p::StructuredIRCode
end

"""Delete an instruction from a block by `Instruction`."""
function Base.delete!(block::Block, inst::Instruction)
    delete!(block.body, inst.ssa_idx)
    return block
end

"""Delete an instruction from a block by SSA index. Throws `KeyError` if absent;
pair with `haskey(block, ssa_idx)` for the idempotent erase pattern."""
Base.delete!(block::Block, ssa_idx::Int) = (delete!(block.body, ssa_idx); block)

"""Whether `block` contains an instruction with the given SSA index."""
Base.haskey(block::Block, ssa_idx::Int) = haskey(block.body, ssa_idx)

"""
    push!(block::Block, stmt, type; flag=0) -> Instruction

Append a new instruction to the block, auto-allocating an SSA index.
Requires `block.parent` to be set (see `_set_parent!`). Optional `flag` is
the per-statement `IR_FLAG_*` bitmask (defaults to 0 / `IR_FLAG_NULL`);
keyword-only to avoid ambiguity with the explicit-idx `push!(block, idx, stmt, type)`.
"""
function Base.push!(block::Block, @nospecialize(stmt), @nospecialize(type);
                    flag::UInt32=UInt32(0))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    push!(block.body, (idx, stmt, type, flag))
    if stmt isa ControlFlowOp
        for b in blocks(stmt)
            b.parent = block
        end
    end
    return Instruction(idx, block)
end

"""
    pushfirst!(block::Block, stmt, type; flag=0) -> Instruction

Prepend a new instruction at the beginning of the block, auto-allocating an SSA index.
"""
function Base.pushfirst!(block::Block, @nospecialize(stmt), @nospecialize(type);
                         flag::UInt32=UInt32(0))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    m = block.body
    pushfirst!(m.ssa_idxes, idx)
    pushfirst!(m.stmts, stmt)
    pushfirst!(m.types, type)
    pushfirst!(m.flags, flag)
    # All existing positions shift up by one; new entry is at position 1.
    for j in 2:length(m.ssa_idxes)
        m.pos_by_idx[m.ssa_idxes[j]] = j
    end
    m.pos_by_idx[idx] = 1
    if stmt isa ControlFlowOp
        for b in blocks(stmt)
            b.parent = block
        end
    end
    return Instruction(idx, block)
end

#=============================================================================
 Statement access — Symbol-keyed on Instruction, NamedTuple-keyed on Block

 Modeled on Core.Compiler.Instruction (`Compiler/src/ssair/ir.jl`): each
 `Instruction` is a thin handle, and reads/writes resolve to the live
 SSAMap entry on every access.

 When swapping a stmt for one with a different opcode, the old `flag` bits
 describe the OLD op and may be stale for the new one. Pass `flag=IR_FLAG_NULL`
 to clear, mirroring LLVM's "fresh instruction, then opt-in `copyIRFlags`"
 pattern (see `Instruction.h:copyIRFlags`). Same-opcode rewrites (only
 operands change) keep the flag.
=============================================================================#

"""
    block[ssa_idx] -> Instruction

Look up the instruction at the given SSA index, returning an `Instruction`
handle. Throws `KeyError` if absent; pair with `haskey(block, ssa_idx)`.
"""
function Base.getindex(block::Block, ssa_idx::Int)
    haskey(block.body, ssa_idx) || throw(KeyError(ssa_idx))
    return Instruction(ssa_idx, block)
end

"""
    block[ssa_idx] = (; stmt=…, type=…, flag=…)

Update one or more fields of the entry at `ssa_idx`. Any subset of
`(:stmt, :type, :flag)` is accepted; fields not mentioned are preserved.
"""
Base.setindex!(block::Block, entry::NamedTuple, ssa_idx::Int) =
    (block.body[ssa_idx] = entry; block)

"""
    inst[:stmt] | inst[:type] | inst[:flag]
    inst[:ssa_idx] | inst[:block]

Read a field of the instruction's live entry in the containing block.
"""
function Base.getindex(inst::Instruction, fld::Symbol)
    fld === :ssa_idx && return inst.ssa_idx
    fld === :block   && return inst.block
    m = inst.block.body
    i = get(m.pos_by_idx, inst.ssa_idx, 0)
    i == 0 && throw(KeyError(inst.ssa_idx))
    fld === :stmt && return m.stmts[i]
    fld === :type && return m.types[i]
    fld === :flag && return m.flags[i]
    throw(ArgumentError("Instruction has no field $fld; expected one of (:stmt, :type, :flag, :ssa_idx, :block)"))
end

"""
    inst[:stmt] = newstmt
    inst[:type] = T
    inst[:flag] = f

Write a single field of the instruction's live entry. Other fields are preserved.
"""
function Base.setindex!(inst::Instruction, @nospecialize(val), fld::Symbol)
    m = inst.block.body
    i = get(m.pos_by_idx, inst.ssa_idx, 0)
    i == 0 && throw(KeyError(inst.ssa_idx))
    if fld === :stmt
        m.stmts[i] = val
    elseif fld === :type
        m.types[i] = val
    elseif fld === :flag
        m.flags[i] = val
    else
        throw(ArgumentError("Instruction setindex! field must be one of (:stmt, :type, :flag), got :$fld"))
    end
    return val
end

"""
    value_type(block::Block, val) -> Any

Get the Julia type of an arbitrary IR value as visible from `block`.

For `SSAValue`, searches the current block then walks up the parent chain.
For `BlockArgument` and `Undef`, returns the type stored on the value.
For `Argument`/`SlotNumber`, looks up in the root `StructuredIRCode.argtypes`.
For `GlobalRef`, queries the binding partition at the SCI's
`valid_worlds.max_world` (see [`const_value`](@ref)).
For constants, returns `typeof(val)`.
Returns `nothing` only for an `SSAValue` or `Argument` whose type cannot be found.
"""
function value_type(block::Block, @nospecialize(val))
    if val isa SSAValue
        entry = get(block.body, val.id, nothing)
        entry !== nothing && return entry.type
        p = block.parent
        while p isa Block
            entry = get(p.body, val.id, nothing)
            entry !== nothing && return entry.type
            p = p.parent
        end
        return nothing
    elseif val isa BlockArgument
        return val.type
    elseif val isa Undef
        return val.type
    elseif val isa Argument
        sci = root(block)
        return val.n <= length(sci.argtypes) ? sci.argtypes[val.n] : nothing
    elseif val isa SlotNumber
        sci = root(block)
        return val.id <= length(sci.argtypes) ? sci.argtypes[val.id] : nothing
    elseif val isa GlobalRef
        sci = root(block)
        return widenconst(global_lattice_element(val, sci.valid_worlds.max_world))
    elseif val isa QuoteNode
        return typeof(val.value)
    else
        return typeof(val)  # literal constant
    end
end

"""
    new_block_arg!(block::Block, type) -> BlockArgument

Add a new BlockArgument to a block, allocating a fresh ID from the root StructuredIRCode.
"""
function new_block_arg!(block::Block, @nospecialize(type))
    sci = root(block)
    sci.max_arg_idx += 1
    arg = BlockArgument(sci.max_arg_idx, type)
    push!(block.args, arg)
    return arg
end

"""
    insert_before!(block::Block, ref::Instruction, stmt, type; flag=0) -> Instruction

Insert a new instruction before `ref`, auto-allocating an SSA index.
"""
function insert_before!(block::Block, ref::Instruction, @nospecialize(stmt), @nospecialize(type);
                        flag::UInt32=UInt32(0))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    insert_before_idx!(block.body, ref.ssa_idx, idx, stmt, type, flag)
    return Instruction(idx, block)
end

function insert_before_idx!(m::SSAMap, before_idx::Int, new_idx::Int, stmt, type,
                            flag::UInt32=UInt32(0))
    pos = get(m.pos_by_idx, before_idx, 0)
    pos == 0 && throw(KeyError(before_idx))
    insert!(m.ssa_idxes, pos, new_idx)
    insert!(m.stmts, pos, stmt)
    insert!(m.types, pos, type)
    insert!(m.flags, pos, flag)
    # Positions ≥ pos have shifted up by one; new entry sits at `pos`.
    for j in pos:length(m.ssa_idxes)
        m.pos_by_idx[m.ssa_idxes[j]] = j
    end
end

"""
    insert_after!(block::Block, ref::Instruction, stmt, type; flag=0) -> Instruction

Insert a new instruction after `ref`, auto-allocating an SSA index.
"""
function insert_after!(block::Block, ref::Instruction, @nospecialize(stmt), @nospecialize(type);
                       flag::UInt32=UInt32(0))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    insert_after_idx!(block.body, ref.ssa_idx, idx, stmt, type, flag)
    return Instruction(idx, block)
end

function insert_after_idx!(m::SSAMap, after_idx::Int, new_idx::Int, stmt, type,
                           flag::UInt32=UInt32(0))
    pos = get(m.pos_by_idx, after_idx, 0)
    pos == 0 && throw(KeyError(after_idx))
    insert!(m.ssa_idxes, pos + 1, new_idx)
    insert!(m.stmts, pos + 1, stmt)
    insert!(m.types, pos + 1, type)
    insert!(m.flags, pos + 1, flag)
    # Positions ≥ pos+1 have shifted up by one; new entry sits at `pos+1`.
    for j in pos+1:length(m.ssa_idxes)
        m.pos_by_idx[m.ssa_idxes[j]] = j
    end
end

"""
    insert_before!(block::Block, ref::SSAValue, stmt, type; flag=0) -> Instruction

Insert a new instruction before the instruction at SSA index `ref.id`.
"""
function insert_before!(block::Block, ref::SSAValue, @nospecialize(stmt), @nospecialize(type);
                        flag::UInt32=UInt32(0))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    insert_before_idx!(block.body, ref.id, idx, stmt, type, flag)
    if stmt isa ControlFlowOp
        for b in blocks(stmt)
            b.parent = block
        end
    end
    return Instruction(idx, block)
end

"""
    insert_after!(block::Block, ref::SSAValue, stmt, type; flag=0) -> Instruction

Insert a new instruction after the instruction at SSA index `ref.id`.
"""
function insert_after!(block::Block, ref::SSAValue, @nospecialize(stmt), @nospecialize(type);
                       flag::UInt32=UInt32(0))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    insert_after_idx!(block.body, ref.id, idx, stmt, type, flag)
    if stmt isa ControlFlowOp
        for b in blocks(stmt)
            b.parent = block
        end
    end
    return Instruction(idx, block)
end


#=============================================================================
 UseRef — handle to a single use site (operand slot)
=============================================================================#

"""
    UseRef

Abstract type for use site handles. All subtypes support `ref[]` (read)
and `ref[] = v` (replace). This hides whether the operand lives in an
Expr arg, a terminator values vector, an init_values vector, etc.
"""
abstract type UseRef end

"""Use site in an indexable container (Vector, Expr.args, etc.)."""
struct IndexedUseRef <: UseRef
    container::Any    # the object holding the value (Vector, Expr, etc.)
    index::Int        # position within the container
end

Base.getindex(r::IndexedUseRef) = _useref_get(r.container, r.index)
Base.setindex!(r::IndexedUseRef, @nospecialize(v)) = _useref_set!(r.container, r.index, v)

_useref_get(v::Vector, i::Int) = v[i]
_useref_get(e::Expr, i::Int) = e.args[i]

_useref_set!(v::Vector, i::Int, @nospecialize(val)) = (v[i] = val)
_useref_set!(e::Expr, i::Int, @nospecialize(val)) = (e.args[i] = val)

#=============================================================================
 walk_uses! — visitor over all use sites (multiple dispatch)
=============================================================================#

# UseRef for mutable struct fields (IfOp.condition, ForOp.lower, etc.)
struct MutableFieldUseRef <: UseRef
    obj::Any
    field::Symbol
end

Base.getindex(r::MutableFieldUseRef) = getfield(r.obj, r.field)
Base.setindex!(r::MutableFieldUseRef, @nospecialize(v)) = setfield!(r.obj, r.field, v)

# Special UseRef for ReturnNode (immutable — replacement creates new ReturnNode)
struct ReturnNodeUseRef <: UseRef
    stmts::Vector{Any}
    pos::Int
end

function Base.getindex(r::ReturnNodeUseRef)
    rn = r.stmts[r.pos]::ReturnNode
    return rn.val
end

function Base.setindex!(r::ReturnNodeUseRef, @nospecialize(v))
    r.stmts[r.pos] = ReturnNode(v)
end

# UseRef for ReturnNode as block terminator (replaces block.terminator)
struct TerminatorReturnNodeUseRef <: UseRef
    block::Block
end

function Base.getindex(r::TerminatorReturnNodeUseRef)
    rn = r.block.terminator::ReturnNode
    return rn.val
end

function Base.setindex!(r::TerminatorReturnNodeUseRef, @nospecialize(v))
    r.block.terminator = ReturnNode(v)
end

# UseRef for PiNode as a statement (immutable — replacement reconstructs it).
struct PiNodeUseRef <: UseRef
    stmts::Vector{Any}
    pos::Int
end

Base.getindex(r::PiNodeUseRef) = (r.stmts[r.pos]::PiNode).val
function Base.setindex!(r::PiNodeUseRef, @nospecialize(v))
    r.stmts[r.pos] = PiNode(v, (r.stmts[r.pos]::PiNode).typ)
end

"""
    walk_uses!(f, node)

Visit every use site (operand slot) in `node` and everything nested below it.
The callback `f` receives a `UseRef` handle for each operand.

Works on any IR node: `Block`, `ControlFlowOp`, `Expr`, terminators.
Always recurses — calling `walk_uses!(f, some_for_op)` walks that ForOp's
own operands plus everything in its body block.
"""
function walk_uses! end

# Block: walk body stmts + terminator
function walk_uses!(f, block::Block)
    for i in 1:length(block.body.ssa_idxes)
        stmt = block.body.stmts[i]
        if stmt isa ControlFlowOp
            walk_uses!(f, stmt)
        elseif stmt isa ReturnNode
            isdefined(stmt, :val) && f(ReturnNodeUseRef(block.body.stmts, i))
        elseif stmt isa PiNode
            # PiNode as a statement wraps a single value with type narrowing.
            f(PiNodeUseRef(block.body.stmts, i))
        elseif is_value_like_stmt(stmt)
            # Alias/forwarding statement: stmt IS a value (SSAValue, BlockArgument,
            # Argument, SlotNumber). Replacement swaps the stmt slot directly.
            f(IndexedUseRef(block.body.stmts, i))
        else
            # Dispatch to user-defined methods for Expr, custom node types, etc.
            walk_uses!(f, stmt)
        end
    end
    term = block.terminator
    if term isa ReturnNode
        # ReturnNode is immutable — use a specialized UseRef that replaces block.terminator
        isdefined(term, :val) && f(TerminatorReturnNodeUseRef(block))
    else
        walk_uses!(f, term)
    end
end

"""A statement whose raw value IS the operand — alias/forwarding form."""
is_value_like_stmt(@nospecialize(s)) =
    s isa SSAValue || s isa BlockArgument || s isa Argument || s isa SlotNumber

# Fallback for unknown statement types (no-op)
walk_uses!(f, ::Any) = nothing

# Expr: walk operands
function walk_uses!(f, expr::Expr)
    start = expr.head === :invoke ? 3 : 2
    for i in start:length(expr.args)
        f(IndexedUseRef(expr.args, i))
    end
end

# Control flow ops: own fields + recurse into blocks
function walk_uses!(f, op::IfOp)
    f(MutableFieldUseRef(op, :condition))
    for b in blocks(op); walk_uses!(f, b); end
end

function walk_uses!(f, op::ForOp)
    f(MutableFieldUseRef(op, :lower))
    f(MutableFieldUseRef(op, :upper))
    f(MutableFieldUseRef(op, :step))
    for i in 1:length(op.init_values); f(IndexedUseRef(op.init_values, i)); end
    for b in blocks(op); walk_uses!(f, b); end
end

function walk_uses!(f, op::Union{WhileOp, LoopOp})
    for i in 1:length(op.init_values); f(IndexedUseRef(op.init_values, i)); end
    for b in blocks(op); walk_uses!(f, b); end
end

# Terminators
function walk_uses!(f, term::Union{ContinueOp, BreakOp, YieldOp})
    vals = operands(term)
    for i in 1:length(vals); f(IndexedUseRef(vals, i)); end
end

function walk_uses!(f, term::ConditionOp)
    f(MutableFieldUseRef(term, :condition))
    args = operands(term)
    for i in 1:length(args); f(IndexedUseRef(args, i)); end
end

# ReturnNode as terminator — handled in Block walk, not here
walk_uses!(f, ::ReturnNode) = nothing

# Nothing terminator
walk_uses!(f, ::Nothing) = nothing


#=============================================================================
 UseIndex — dict-like index mapping values to their use sites
=============================================================================#

"""
    UseIndex

Pre-built index mapping values to their use sites. Created by `uses(block)`.
Supports `idx[val]` to get use sites, `haskey(idx, val)` for liveness checks.

Accepts any key type that appears in operand positions: `SSAValue`,
`BlockArgument`, `Argument`, `Instruction`, etc.
"""
struct UseIndex
    index::Dict{Any, Vector{UseRef}}
end

function Base.getindex(idx::UseIndex, @nospecialize(key))
    k = normalize_key(key)
    return get(idx.index, k, UseRef[])
end

Base.haskey(idx::UseIndex, @nospecialize(key)) = haskey(idx.index, normalize_key(key))

# Normalize keys so that SSAValue(5) and Instruction(5,...) map to the same entry
normalize_key(v::SSAValue) = v
normalize_key(v::Instruction) = SSAValue(v.ssa_idx)
normalize_key(@nospecialize(v)) = v


#=============================================================================
 uses() — the public API
=============================================================================#

export uses, users, replace_uses!

"""
    uses(block::Block) -> UseIndex

Build a use index for all use sites in `block` (recursively).
Returns a dict-like object: `idx[val]` gives the `Vector{UseRef}` of all
sites referencing `val`.
"""
function uses(block::Block)
    index = Dict{Any, Vector{UseRef}}()
    walk_uses!(block) do ref
        val = ref[]
        val === nothing && return
        key = normalize_key(val)
        refs = get!(Vector{UseRef}, index, key)
        push!(refs, ref)
    end
    return UseIndex(index)
end

"""
    uses(block::Block, val) -> Vector{UseRef}

Find all use sites of `val` in `block` (recursively). Linear scan — for
repeated queries, prefer building a `UseIndex` via `uses(block)`.
"""
function uses(block::Block, @nospecialize(val))
    result = UseRef[]
    target = normalize_key(val)
    walk_uses!(block) do ref
        normalize_key(ref[]) == target && push!(result, ref)
    end
    return result
end

"""
    replace_uses!(block::Block, old, new_val)

Replace all uses of `old` with `new_val` in `block` (recursively).
`old` can be any value type (SSAValue, BlockArgument, Instruction).
"""
function replace_uses!(block::Block, @nospecialize(old), @nospecialize(new_val))
    target = normalize_key(old)
    walk_uses!(block) do ref
        normalize_key(ref[]) == target && (ref[] = new_val)
    end
end

"""
    users(block::Block, val) -> Vector{Instruction}

Find all instructions in `block` (recursively) that reference `val` as an
operand. Returns `Instruction` objects — the analog of MLIR's
`Value::getUsers()` which maps use-sites to owning operations.

See also `uses(block, val)` which returns `UseRef`s (use-sites).
"""
function users(block::Block, @nospecialize(val))
    target = normalize_key(val)
    result = Instruction[]
    seen = Set{Int}()
    for b in eachblock(block)
        for inst in instructions(b)
            inst.ssa_idx in seen && continue
            _references(inst[:stmt], target) || continue
            push!(seen, inst.ssa_idx)
            push!(result, inst)
        end
    end
    return result
end

"""Check if a statement references `target` in any operand position."""
function _references(@nospecialize(stmt), @nospecialize(target))
    if stmt isa Expr
        start = stmt.head === :invoke ? 3 : 2
        for i in start:length(stmt.args)
            normalize_key(stmt.args[i]) == target && return true
        end
    elseif stmt isa ControlFlowOp
        # Check control flow operands (init values, conditions, etc.)
        if stmt isa IfOp
            normalize_key(stmt.condition) == target && return true
        elseif stmt isa ForOp
            normalize_key(stmt.lower) == target && return true
            normalize_key(stmt.upper) == target && return true
            normalize_key(stmt.step) == target && return true
            for v in stmt.init_values
                normalize_key(v) == target && return true
            end
        elseif stmt isa Union{WhileOp, LoopOp}
            for v in stmt.init_values
                normalize_key(v) == target && return true
            end
        end
    elseif stmt isa ReturnNode
        isdefined(stmt, :val) || return false
        normalize_key(stmt.val) == target && return true
    elseif stmt isa PiNode
        normalize_key(stmt.val) == target && return true
    elseif is_value_like_stmt(stmt)
        # Alias statement: the stmt itself is the referenced value.
        normalize_key(stmt) == target && return true
    end
    return false
end


#=============================================================================
 Loop carries abstraction
=============================================================================#

export carries, init_value, body_arg, term_value, init_value!, term_value!

const LoopOps = Union{ForOp, LoopOp, WhileOp}

"""
    LoopCarries(op::Union{ForOp, LoopOp, WhileOp})

View over a loop op's carried values. Encapsulates the 4-way positional
coupling between init_values, body args, and terminator values.

Supports iteration (yields `CarryRef` handles), indexed access, and
bulk removal via `filter!`/`deleteat!`.
"""
struct LoopCarries
    op::LoopOps
    terminators::Vector{Terminator}
end

"""
    carries(op::Union{ForOp, LoopOp, WhileOp}) -> LoopCarries

Get a view over the loop's carried values. Supports iteration, indexed
access, `filter!`, `deleteat!`, and `push!`.
"""
carries(op::ForOp) = LoopCarries(op, reachable_terminators(op.body))
carries(op::LoopOp) = LoopCarries(op, reachable_terminators(op.body))
carries(op::WhileOp) = LoopCarries(op, [reachable_terminators(op.before); reachable_terminators(op.after)])

"""
    CarryRef(carries, index)

Handle to a single loop carry at position `index`. Provides read/write access
to the init value, body arg, and terminator values for this carry.
"""
struct CarryRef
    carries::LoopCarries
    index::Int
end

"""Get the body block for a loop op."""
body_block(op::ForOp) = op.body
body_block(op::LoopOp) = op.body
body_block(op::WhileOp) = op.before  # carries enter through before block

"""Get the init value for this carry."""
init_value(c::CarryRef) = c.carries.op.init_values[c.index]

"""Get the body BlockArgument for this carry."""
function body_arg(c::CarryRef)
    op = c.carries.op
    block = body_block(op)
    block.args[c.index]
end

"""Get the after-region BlockArgument for this carry (WhileOp only)."""
after_arg(c::CarryRef) = (c.carries.op::WhileOp).after.args[c.index]

"""Get the terminator value for this carry from a specific terminator."""
term_value(c::CarryRef, t) = operands(t)[c.index]

"""Set the init value for this carry."""
init_value!(c::CarryRef, val) = (c.carries.op.init_values[c.index] = val; val)

"""Set the terminator value for this carry in a specific terminator."""
term_value!(c::CarryRef, t, val) = (operands(t)[c.index] = val)

# Iteration
Base.length(c::LoopCarries) = length(c.op.init_values)
Base.iterate(c::LoopCarries, i::Int=1) = i > length(c) ? nothing : (CarryRef(c, i), i + 1)
Base.getindex(c::LoopCarries, i::Int) = CarryRef(c, i)
Base.eltype(::Type{LoopCarries}) = CarryRef
Base.firstindex(::LoopCarries) = 1
Base.lastindex(c::LoopCarries) = length(c)

"""
    filter!(pred, carries::LoopCarries) -> Dict{Int, Int}

Keep only carries where `pred(CarryRef)` returns true. Removes the
corresponding init_values, body args, and terminator values at all sites.

Returns a mapping from old carry index to new carry index, useful for
renumbering external references (e.g., getfield extractions).
"""
function Base.filter!(pred, carries::LoopCarries)
    keep = BitVector(pred(CarryRef(carries, i)) for i in 1:length(carries))
    remove_carries!(carries, keep)
end

"""
    deleteat!(carries::LoopCarries, indices) -> Dict{Int, Int}

Remove carries at the given indices. `indices` can be a vector of Ints,
a Set{Int}, or a BitVector (where true means delete).

Returns old→new index mapping.
"""
function Base.deleteat!(carries::LoopCarries, indices)
    n = length(carries)
    keep = trues(n)
    for i in indices
        keep[i] = false
    end
    remove_carries!(carries, keep)
end

"""Internal: remove carries based on keep mask. Returns old→new mapping."""
function remove_carries!(carries::LoopCarries, keep::BitVector)
    op = carries.op
    n = length(carries)
    @assert length(keep) == n

    # Build old→new index mapping
    old_to_new = Dict{Int, Int}()
    new_idx = 0
    for old_idx in 1:n
        if keep[old_idx]
            new_idx += 1
            old_to_new[old_idx] = new_idx
        end
    end

    # Find indices to remove (in reverse for safe deleteat!)
    to_remove = sort([i for i in 1:n if !keep[i]], rev=true)
    isempty(to_remove) && return old_to_new

    body = body_block(op)

    for i in to_remove
        # Remove init value
        deleteat!(op.init_values, i)

        # Remove body arg
        deleteat!(body.args, i)

        # Remove from all reachable terminators
        for term in carries.terminators
            ops = operands(term)
            if i <= length(ops)
                deleteat!(ops, i)
            end
        end

        # WhileOp: also remove from after block args
        if op isa WhileOp
            deleteat!(op.after.args, i)
        end
    end

    return old_to_new
end

"""
    push!(carries::LoopCarries, init_val, body_arg_type) -> CarryRef

Append a new carry to the loop. Creates a new BlockArgument for the body,
pushes init_val, and threads the new arg through all reachable terminators.

Returns a CarryRef to the new carry.
"""
function Base.push!(carries::LoopCarries, init_val, @nospecialize(body_arg_type))
    op = carries.op
    body = body_block(op)

    new_arg = new_block_arg!(body, body_arg_type)

    push!(op.init_values, init_val)

    # Thread through all reachable terminators
    for term in carries.terminators
        push!(operands(term), new_arg)
    end

    # WhileOp: also add to after block args
    if op isa WhileOp
        after_arg = new_block_arg!(op.after, body_arg_type)
    end

    return CarryRef(carries, length(op.init_values))
end


#=============================================================================
 Block traversal
=============================================================================#

"""
    reachable_terminators(block::Block) -> Vector{Terminator}

Collect the block's own terminator plus all loop exits reachable through
nested IfOps. Each terminator type is scoped to a specific parent:
ContinueOp/BreakOp target the enclosing loop, while YieldOp targets the
nearest enclosing result-producing op. Because IfOp captures YieldOp, only
ContinueOp/BreakOp are visible through nested IfOps.
"""
function reachable_terminators(outer::Block)
    result = Terminator[]

    # outer terminator.
    # we have to include yield/condition here because outer may be an IfOp
    let
        term = outer.terminator
        if term isa ContinueOp || term isa BreakOp || term isa YieldOp || term isa ConditionOp
            push!(result, term)
        end
    end

    # nested terminators reachable through nested IfOps.
    # we have to ignore yield/condition here because that's inner to the IfOp
    function collect_terminators!(inner::Block)
        term = inner.terminator
        if term isa ContinueOp || term isa BreakOp
            push!(result, term)
        end
        for (_, entry) in inner.body
            if entry.stmt isa IfOp
                for b in blocks(entry.stmt)
                    collect_terminators!(b)
                end
            end
        end
    end
    for (_, entry) in outer.body
        if entry.stmt isa IfOp
            for b in blocks(entry.stmt)
                collect_terminators!(b)
            end
        end
    end

    return result
end

"""
    eachblock(sci::StructuredIRCode) -> Vector{Block}
    eachblock(root::Block) -> Vector{Block}

Pre-order traversal of all blocks in the IR, recursing into nested control flow ops.
"""
eachblock(sci::StructuredIRCode) = eachblock(sci.entry)

function eachblock(root::Block)
    result = Block[]
    _collect_blocks!(result, root)
    return result
end

function _collect_blocks!(out, block::Block)
    push!(out, block)
    for (_, entry) in block.body
        entry.stmt isa ControlFlowOp || continue
        for b in blocks(entry.stmt)
            _collect_blocks!(out, b)
        end
    end
end

"""
    findblock(sci::StructuredIRCode, inst::Instruction) -> Union{Block, Nothing}

Find the Block containing the given instruction.
Returns `nothing` if not found.
"""
function findblock(sci::StructuredIRCode, inst::Instruction)
    found = nothing
    walk(sci) do i, block
        if i.ssa_idx == inst.ssa_idx
            found = block
            return :interrupt
        end
    end
    return found
end


#=============================================================================
 walk — operation/block walker with control flow (cf. MLIR walk())
=============================================================================#

"""
    walk(f, root::Union{Block, StructuredIRCode}; order=:preorder)

Walk all instructions, calling `f(inst, block)` for each. The callback
returns a `Symbol` controlling traversal:

- `:advance` — continue normally (default if callback returns `nothing`)
- `:skip` — do not recurse into this op's sub-blocks (only meaningful for `ControlFlowOp`s)
- `:interrupt` — stop the walk immediately

Supports `:preorder` (visit before recursing, default) and `:postorder`
(visit after recursing). Analogous to MLIR's `walk()` with `WalkOrder`
and `WalkResult`.
"""
function walk(f, root::Union{Block, StructuredIRCode}; order::Symbol=:preorder)
    block = root isa StructuredIRCode ? root.entry : root
    order === :preorder  && return _walk_pre!(f, block)
    order === :postorder && return _walk_post!(f, block)
    throw(ArgumentError("walk: order must be :preorder or :postorder, got :$order"))
end

function _walk_pre!(f, block::Block)
    for inst in instructions(block)
        result = f(inst, block)
        result === :interrupt && return :interrupt
        s = inst[:stmt]
        if s isa ControlFlowOp && result !== :skip
            for b in blocks(s)
                _walk_pre!(f, b) === :interrupt && return :interrupt
            end
        end
    end
    return :advance
end

function _walk_post!(f, block::Block)
    for inst in instructions(block)
        s = inst[:stmt]
        if s isa ControlFlowOp
            for b in blocks(s)
                _walk_post!(f, b) === :interrupt && return :interrupt
            end
        end
        result = f(inst, block)
        result === :interrupt && return :interrupt
        # :skip is meaningless in postorder (children already visited)
    end
    return :advance
end


#=============================================================================
 Expression inspection
=============================================================================#

"""
    resolve_call(block::Block, stmt) -> (resolved_func, operands) or nothing
    resolve_call(block::Block, inst::Instruction) -> (resolved_func, operands) or nothing

Extract the resolved function and operands from a `:call` or `:invoke` Expr.
For `:call`, `stmt.args[1]` is the function reference and args 2+ are operands.
For `:invoke`, `stmt.args[2]` is the function reference and args 3+ are operands.

The callee is resolved via its inferred type using `singleton_type` — the same
mechanism Julia's compiler uses during inlining. This handles GlobalRef, literal
values, and SSAValue callees whose type is a singleton function type.

Returns `nothing` if `stmt` is not a call expression or the function cannot be resolved.
"""
function resolve_call(block::Block, @nospecialize(stmt))
    stmt isa Expr || return nothing
    if stmt.head === :call
        func_ref = stmt.args[1]
        operands = @view stmt.args[2:end]
    elseif stmt.head === :invoke
        func_ref = stmt.args[2]
        operands = @view stmt.args[3:end]
    else
        return nothing
    end
    resolved = resolve_callee(block, func_ref)
    resolved === nothing && return nothing
    return (resolved, operands)
end

resolve_call(block::Block, inst::Instruction) = resolve_call(block, inst[:stmt])

"""
    resolve_callee(block::Block, ref) -> resolved_func or nothing

Resolve a callee reference to a concrete function value. Uses `singleton_type`
on the inferred type (mirroring Julia's compiler) for symbolic refs (SSAValue,
Argument, BlockArgument, SlotNumber). Falls back to evaluating GlobalRef and
literal values directly — necessary for non-singleton types like
`Core.IntrinsicFunction` where all intrinsics share one type and
`singleton_type` returns `nothing`. Julia's inliner sometimes substitutes a
`GlobalRef(Core.Intrinsics, :sub_float)` callee with the literal
`IntrinsicFunction` value (e.g. when inlining cross-module wrappers like
`BFloat16s.:-`), so non-symbolic refs are returned as-is.
"""
function resolve_callee(block::Block, @nospecialize(ref))
    if ref isa SSAValue || ref isa Argument || ref isa BlockArgument || ref isa SlotNumber
        T = value_type(block, ref)
        T === nothing && return nothing
        return Core.Compiler.singleton_type(T)
    end
    # GlobalRefs in optimized IR are guaranteed valid — inference rejects undefined bindings.
    ref isa GlobalRef && return getfield(ref.mod, ref.name)
    ref isa QuoteNode && return ref.value
    # Literal callable embedded directly as args[1] (e.g. an IntrinsicFunction
    # value substituted by Julia's inliner): the ref *is* the function.
    return ref
end

"""
    iscall(stmt) -> Bool

Check whether a statement is a `:call` or `:invoke` expression.
"""
iscall(@nospecialize(stmt)) = stmt isa Expr && (stmt.head === :call || stmt.head === :invoke)

"""
    iscall(inst::Instruction) -> Bool

Convenience overload: checks the underlying statement.
"""
iscall(inst::Instruction) = iscall(inst[:stmt])

"""
    callee(stmt::Expr) -> Any

Get the raw function reference from a `:call` or `:invoke` expression.
For `:call`, returns `stmt.args[1]`. For `:invoke`, returns `stmt.args[2]`.
Does NOT resolve GlobalRef — use `resolve_call` for that.
"""
function callee(stmt::Expr)
    if stmt.head === :call
        return stmt.args[1]
    elseif stmt.head === :invoke
        return stmt.args[2]
    end
    throw(ArgumentError("callee() requires a :call or :invoke Expr, got :$(stmt.head)"))
end

"""
    callee(inst::Instruction) -> Any

Convenience overload: extracts callee from the underlying statement.
"""
callee(inst::Instruction) = callee(inst[:stmt]::Expr)

"""
    callargs(stmt::Expr) -> SubArray

Get the operand arguments of a `:call` or `:invoke` expression (excludes function ref).
Returns a view into `stmt.args`.
"""
function callargs(stmt::Expr)
    if stmt.head === :call
        return @view stmt.args[2:end]
    elseif stmt.head === :invoke
        return @view stmt.args[3:end]
    end
    throw(ArgumentError("callargs() requires a :call or :invoke Expr, got :$(stmt.head)"))
end

"""
    callargs(inst::Instruction) -> SubArray

Convenience overload: extracts call arguments from the underlying statement.
"""
callargs(inst::Instruction) = callargs(inst[:stmt]::Expr)


#=============================================================================
 Instruction operands
=============================================================================#

"""
    operands(block::Block, inst::Instruction) -> Vector{Any}
    operands(block::Block, stmt) -> Vector{Any}

Extract data operands from an instruction's statement — the values the
instruction consumes. Handles `PiNode` and `ControlFlowOp` types natively.
Returns `Any[]` for unknown statement types.

Extend via `operands(::Block, s::MyType)` for domain-specific IR nodes.
"""
operands(block::Block, inst::Instruction) = operands(block, inst[:stmt])

operands(::Block, s::PiNode) = Any[s.val]
operands(::Block, s::ControlFlowOp) = operands(s)
# Alias statements (stmt IS a value) forward the value itself as their sole operand.
operands(::Block, s::SSAValue) = Any[s]
operands(::Block, s::BlockArgument) = Any[s]
operands(::Block, s::Argument) = Any[s]
operands(::Block, s::SlotNumber) = Any[s]
function operands(::Block, s::Expr)
    if s.head === :call
        return @view s.args[2:end]
    elseif s.head === :invoke
        return @view s.args[3:end]
    elseif s.head === :new || s.head === :splatnew
        return @view s.args[2:end]
    else
        return s.args
    end
end
operands(::Block, @nospecialize(_)) = Any[]


#=============================================================================
 Definition lookup
=============================================================================#

"""
    def(root, val::Core.SSAValue) -> Union{Instruction, Nothing}

Find the instruction that defines `val`. Performs a linear scan over
all blocks. The instruction's `block` field gives the containing block.
For repeated queries, build an index via [`defs`](@ref) instead.
"""
function def(root::Union{Block, StructuredIRCode}, val::Core.SSAValue)
    blk = root isa StructuredIRCode ? root.entry : root
    target = val.id
    for b in eachblock(blk)
        for inst in instructions(b)
            inst.ssa_idx == target && return inst
        end
    end
    return nothing
end

"""
    DefIndex

Pre-built index mapping SSA indices to their defining `Instruction`.
Build via `defs(root)`, query via `def(idx, val)`.
Analogous to `UseIndex` / `uses(block)`.
"""
struct DefIndex
    map::Dict{Int, Instruction}
end

"""
    defs(root) -> DefIndex

Build a definition index for all instructions in `root` (recursively).
Returns a `DefIndex` that supports O(1) lookup via `def(idx, val)`.

Analogous to `uses(block)` which returns a `UseIndex`.
"""
function defs(root::Union{Block, StructuredIRCode})
    blk = root isa StructuredIRCode ? root.entry : root
    map = Dict{Int, Instruction}()
    for b in eachblock(blk)
        for inst in instructions(b)
            map[inst.ssa_idx] = inst
        end
    end
    return DefIndex(map)
end

"""
    def(idx::DefIndex, val::Core.SSAValue) -> Union{Instruction, Nothing}

O(1) lookup of the instruction defining `val`.
"""
def(idx::DefIndex, val::Core.SSAValue) = get(idx.map, val.id, nothing)

Base.haskey(idx::DefIndex, val::Core.SSAValue) = haskey(idx.map, val.id)


#=============================================================================
 Scope queries
=============================================================================#

"""
    is_defined_outside(val, block::Block) -> Bool
    is_defined_outside(val, op::ForOp) -> Bool
    is_defined_outside(val, op::WhileOp) -> Bool
    is_defined_outside(val, op::LoopOp) -> Bool

Check whether `val` is defined outside a block (and all its descendants),
or outside a loop operation's regions.

The loop-op overloads handle values that are conceptually "inside" the loop
but not stored in a block's args — e.g., `ForOp.iv_arg`.

`Argument`s (function parameters), constants, `GlobalRef`s, and other
non-SSA values are always considered outside.

Analogous to MLIR's `LoopLikeOpInterface::isDefinedOutsideOfLoop`.
"""
function is_defined_outside(@nospecialize(val), block::Block)
    if val isa SSAValue
        for b in eachblock(block)
            val ∈ b && return false
        end
        return true
    elseif val isa BlockArgument
        for b in eachblock(block)
            val ∈ b && return false
        end
        return true
    else
        return true
    end
end

function is_defined_outside(@nospecialize(val), op::ForOp)
    val === op.iv_arg && return false
    return is_defined_outside(val, op.body)
end

function is_defined_outside(@nospecialize(val), op::WhileOp)
    return is_defined_outside(val, op.before) && is_defined_outside(val, op.after)
end

function is_defined_outside(@nospecialize(val), op::LoopOp)
    return is_defined_outside(val, op.body)
end


#=============================================================================
 Instruction movement
=============================================================================#

"""
    move_before!(inst::Instruction, target::Instruction) -> Instruction

Move `inst` from its current block to just before `target` in `target`'s block.
The instruction retains its SSA index, statement, type, and flags. Sub-block
parents are updated if the instruction is a `ControlFlowOp`. Returns a fresh
handle pointing into the destination block.

Analogous to MLIR's `Operation::moveBefore`.
"""
function move_before!(inst::Instruction, target::Instruction)
    src = inst.block
    dst = target.block
    entry = src.body[inst.ssa_idx]

    delete!(src.body, inst.ssa_idx)
    insert_before_idx!(dst.body, target.ssa_idx, inst.ssa_idx,
                       entry.stmt, entry.type, entry.flag)

    if entry.stmt isa ControlFlowOp
        for b in blocks(entry.stmt)
            b.parent = dst
        end
    end
    return Instruction(inst.ssa_idx, dst)
end

"""
    move_after!(inst::Instruction, target::Instruction) -> Instruction

Move `inst` from its current block to just after `target` in `target`'s block.
The instruction retains its SSA index, statement, type, and flags. Sub-block
parents are updated if the instruction is a `ControlFlowOp`. Returns a fresh
handle pointing into the destination block.

Analogous to MLIR's `Operation::moveAfter`.
"""
function move_after!(inst::Instruction, target::Instruction)
    src = inst.block
    dst = target.block
    entry = src.body[inst.ssa_idx]

    delete!(src.body, inst.ssa_idx)
    insert_after_idx!(dst.body, target.ssa_idx, inst.ssa_idx,
                      entry.stmt, entry.type, entry.flag)

    if entry.stmt isa ControlFlowOp
        for b in blocks(entry.stmt)
            b.parent = dst
        end
    end
    return Instruction(inst.ssa_idx, dst)
end


#=============================================================================
 Static-eval helpers
=============================================================================#

"""
    const_value(sci::StructuredIRCode, x) -> Union{Some, Nothing}

Return `Some(value)` when `x`'s value is statically known in `sci`,
otherwise `nothing`. The Julia analog of `static_eval` in `codegen.cpp`:
dispatches on every operand-position IR shape, recovers the value from
inference's lattice when it's a `Const` or singleton, and returns the
literal itself otherwise.

`GlobalRef` lookups are anchored on `sci.valid_worlds` (captured at
structurization from `IRCode.valid_worlds`) and read only binding-
partition metadata — never `getfield(mod, name)`. So on 1.12+ this
neither triggers the "access-to-binding-prior-to-its-definition-world"
warning nor reflects post-inference rebinds.
"""
function const_value(sci::StructuredIRCode, @nospecialize(x))
    x isa GlobalRef            && return from_type(global_lattice_element(x, sci.valid_worlds.max_world))
    x isa QuoteNode            && return Some(x.value)
    x isa Instruction          && return from_type(x[:type])
    x isa BlockArgument        && return from_type(x.type)
    x isa Core.SSAValue        && return const_value_ssa(sci, x)
    x isa Core.Argument        && return (1 <= x.n <= length(sci.argtypes) ?
                                           from_type(sci.argtypes[x.n]) : nothing)
    # `MethodInstance` (and `CodeInstance`) appear as the first operand
    # of `:invoke` Exprs but they're inference artifacts, not values
    # — match `static_eval` (codegen.cpp:3245–46) by rejecting them
    # explicitly so they don't fall through to the "literal" branch.
    x isa Core.MethodInstance  && return nothing
    x isa Core.CodeInstance    && return nothing
    # Anything else — `x` is a literal, the value is itself.
    return Some(x)
end

# Resolve an `SSAValue` storage tag to its def's type. Linear-scans
# `eachblock` like `def`, just without materializing an `Instruction`.
function const_value_ssa(sci::StructuredIRCode, ssa::Core.SSAValue)
    inst = def(sci, ssa)
    inst === nothing ? nothing : from_type(inst[:type])
end

# Internal: recover the value from a type slot. Handles both
# `Compiler.Const(val)` (inference-narrowed to a specific value) and
# singleton ghost types (one-instance types like `typeof(sin)`).
# Mirrors `singleton_type` + `Const`-unwrap in one helper.
function from_type(@nospecialize(rt))
    rt === nothing && return nothing
    rt isa Core.Compiler.Const && return Some(rt.val)
    if rt isa Type && isdefined(rt, :instance)
        return Some(rt.instance)
    end
    return nothing
end

# Internal: read a `GlobalRef`'s inferred lattice element at `world`.
# Mirrors `Core.Compiler.abstract_eval_globalref_type`. Lattice elements
# aren't part of the public surface; consumers go through `const_value`.
@static if VERSION >= v"1.12-"
    function global_lattice_element(g::GlobalRef, world::UInt)
        binding = convert(Core.Binding, g)
        partition = Core.Compiler.lookup_binding_partition(world, binding)
        (_, (leaf_binding, leaf_partition)) =
            Core.Compiler.walk_binding_partition(binding, partition, world)
        return Core.Compiler.abstract_eval_partition_load(nothing, leaf_binding, leaf_partition).rt
    end
else
    # 1.11 lacks the binding-partition API and doesn't have the world-age
    # binding-access warning either, so the direct lookup is safe and the
    # value (via `Const`) reflects the current binding state.
    global_lattice_element(g::GlobalRef, ::UInt) = Core.Compiler.Const(getfield(g.mod, g.name))
end
