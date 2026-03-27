# Utilities for structured IR
#
# Block mutation: parent, root, push!, insert_before!, insert_after!, delete!
# Block traversal: eachblock, block_for_inst
# Use tracking: uses(), replace_uses!
# Loop carries: carries()


#=============================================================================
 Block mutation (SSA-allocating operations)
=============================================================================#

public root, parent
export insert_before!, insert_after!, eachblock, block_for_inst

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

"""Delete an instruction from a block by `Inst`."""
function Base.delete!(block::Block, inst::Inst)
    delete!(block.body, inst.ssa_idx)
    return block
end

"""
    push!(block::Block, stmt, typ) -> Inst

Append a new instruction to the block, auto-allocating an SSA index.
Requires `block.parent` to be set (see `_set_parent!`).
"""
function Base.push!(block::Block, @nospecialize(stmt), @nospecialize(typ))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    push!(block.body, (idx, stmt, typ))
    if stmt isa ControlFlowOp
        for b in blocks(stmt)
            b.parent = block
        end
    end
    return Inst(idx, stmt, typ)
end

"""
    insert_before!(block::Block, ref::Inst, stmt, typ) -> Inst

Insert a new instruction before `ref`, auto-allocating an SSA index.
"""
function insert_before!(block::Block, ref::Inst, @nospecialize(stmt), @nospecialize(typ))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    insert_before_idx!(block.body, ref.ssa_idx, idx, stmt, typ)
    return Inst(idx, stmt, typ)
end

function insert_before_idx!(m::SSAMap, before_idx::Int, new_idx::Int, stmt, typ)
    pos = findfirst(==(before_idx), m.ssa_idxes)
    pos === nothing && throw(KeyError(before_idx))
    insert!(m.ssa_idxes, pos, new_idx)
    insert!(m.stmts, pos, stmt)
    insert!(m.types, pos, typ)
end

"""
    insert_after!(block::Block, ref::Inst, stmt, typ) -> Inst

Insert a new instruction after `ref`, auto-allocating an SSA index.
"""
function insert_after!(block::Block, ref::Inst, @nospecialize(stmt), @nospecialize(typ))
    sci = root(block)
    sci.max_ssa_idx += 1
    idx = sci.max_ssa_idx
    insert_after_idx!(block.body, ref.ssa_idx, idx, stmt, typ)
    return Inst(idx, stmt, typ)
end

function insert_after_idx!(m::SSAMap, after_idx::Int, new_idx::Int, stmt, typ)
    pos = findfirst(==(after_idx), m.ssa_idxes)
    pos === nothing && throw(KeyError(after_idx))
    insert!(m.ssa_idxes, pos + 1, new_idx)
    insert!(m.stmts, pos + 1, stmt)
    insert!(m.types, pos + 1, typ)
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
        elseif stmt isa Expr
            walk_uses!(f, stmt)
        elseif stmt isa ReturnNode
            isdefined(stmt, :val) && f(ReturnNodeUseRef(block.body.stmts, i))
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
    for i in 1:length(term.values); f(IndexedUseRef(term.values, i)); end
end

function walk_uses!(f, term::ConditionOp)
    f(MutableFieldUseRef(term, :condition))
    for i in 1:length(term.args); f(IndexedUseRef(term.args, i)); end
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

Accepts any key type that appears in operand positions: `Int` (treated as
SSAValue index), `SSAValue`, `BlockArg`, `Argument`, etc.
"""
struct UseIndex
    index::Dict{Any, Vector{UseRef}}
end

function Base.getindex(idx::UseIndex, @nospecialize(key))
    k = normalize_key(key)
    return get(idx.index, k, UseRef[])
end

Base.haskey(idx::UseIndex, @nospecialize(key)) = haskey(idx.index, normalize_key(key))

# Normalize keys so that SSAValue(5), plain Int 5, and Inst(5,...) map to the same entry
normalize_key(v::SSAValue) = v
normalize_key(v::Int) = SSAValue(v)
normalize_key(v::Inst) = SSAValue(v.ssa_idx)
normalize_key(@nospecialize(v)) = v


#=============================================================================
 uses() — the public API
=============================================================================#

export uses, replace_uses!

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
`old` can be any value type (SSAValue, BlockArg, Inst, Int).
"""
function replace_uses!(block::Block, @nospecialize(old), @nospecialize(new_val))
    target = normalize_key(old)
    walk_uses!(block) do ref
        normalize_key(ref[]) == target && (ref[] = new_val)
    end
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
carries(op::ForOp) = LoopCarries(op, terminators(op.body))
carries(op::LoopOp) = LoopCarries(op, terminators(op.body))
carries(op::WhileOp) = LoopCarries(op, [terminators(op.before); terminators(op.after)])

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

"""Get the body BlockArg for this carry."""
function body_arg(c::CarryRef)
    op = c.carries.op
    block = body_block(op)
    block.args[c.index]
end

"""Get the terminator value for this carry from a specific terminator."""
function term_value(c::CarryRef, t::Union{ContinueOp, BreakOp, YieldOp})
    t.values[c.index]
end
function term_value(c::CarryRef, t::ConditionOp)
    t.args[c.index]
end

"""Set the init value for this carry."""
init_value!(c::CarryRef, val) = (c.carries.op.init_values[c.index] = val; val)

"""Set the terminator value for this carry in a specific terminator."""
function term_value!(c::CarryRef, t::Union{ContinueOp, BreakOp, YieldOp}, val)
    t.values[c.index] = val
end
function term_value!(c::CarryRef, t::ConditionOp, val)
    t.args[c.index] = val
end

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
            if term isa ContinueOp || term isa BreakOp || term isa YieldOp
                if i <= length(term.values)
                    deleteat!(term.values, i)
                end
            elseif term isa ConditionOp
                if i <= length(term.args)
                    deleteat!(term.args, i)
                end
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

Append a new carry to the loop. Creates a new BlockArg for the body,
pushes init_val, and threads the new arg through all reachable terminators.

Returns a CarryRef to the new carry.
"""
function Base.push!(carries::LoopCarries, init_val, @nospecialize(body_arg_type))
    op = carries.op
    body = body_block(op)

    # Allocate a new BlockArg ID
    next_id = isempty(body.args) ? 1 : maximum(a.id for a in body.args) + 1
    new_arg = BlockArg(next_id, body_arg_type)

    push!(op.init_values, init_val)
    push!(body.args, new_arg)

    # Thread through all reachable terminators
    for term in carries.terminators
        if term isa ContinueOp || term isa BreakOp || term isa YieldOp
            push!(term.values, new_arg)
        elseif term isa ConditionOp
            push!(term.args, new_arg)
        end
    end

    # WhileOp: also add to after block args
    if op isa WhileOp
        after_id = isempty(op.after.args) ? 1 : maximum(a.id for a in op.after.args) + 1
        after_arg = BlockArg(after_id, body_arg_type)
        push!(op.after.args, after_arg)
    end

    return CarryRef(carries, length(op.init_values))
end


#=============================================================================
 Block traversal
=============================================================================#

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
    block_for_inst(sci::StructuredIRCode, ssa_idx::Int) -> Union{Block, Nothing}

Find the Block containing the instruction with the given SSA index.
Returns `nothing` if not found.
"""
function block_for_inst(sci::StructuredIRCode, ssa_idx::Int)
    for block in eachblock(sci)
        haskey(block.body, ssa_idx) && return block
    end
    return nothing
end
