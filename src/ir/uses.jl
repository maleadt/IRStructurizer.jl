#=============================================================================
 UseRef: handle to a single use site (operand slot)
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
 walk_uses!: visitor over all use sites (multiple dispatch)
=============================================================================#

# UseRef for mutable struct fields (IfOp.condition, ForOp.lower, etc.)
struct MutableFieldUseRef <: UseRef
    obj::Any
    field::Symbol
end

Base.getindex(r::MutableFieldUseRef) = getfield(r.obj, r.field)
Base.setindex!(r::MutableFieldUseRef, @nospecialize(v)) = setfield!(r.obj, r.field, v)

# UseRef for ReturnNode. ReturnNode is immutable, so replacement creates a new one.
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

# UseRef for PiNode as a statement. PiNode is immutable, so replacement reconstructs it.
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
Always recurses: calling `walk_uses!(f, some_for_op)` walks that ForOp's
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
        # ReturnNode is immutable; the UseRef replaces block.terminator.
        isdefined(term, :val) && f(TerminatorReturnNodeUseRef(block))
    else
        walk_uses!(f, term)
    end
end

"""A statement whose raw value IS the operand (alias/forwarding form)."""
is_value_like_stmt(@nospecialize(s)) =
    s isa SSAValue || s isa BlockArgument || s isa Argument || s isa SlotNumber

# Fallback for unknown statement types (no-op)
walk_uses!(f, ::Any) = nothing

# Expr: walk operands. For `:invoke`, args are [CodeInstance/MI, callee, args...];
# the callee (args[2]) is a real SSA use (e.g. a closure being applied) and must
# be walked, so start at 2. The CodeInstance/MI at args[1] is not a value, so
# skipping it is correct for both `:invoke` and `:call`.
function walk_uses!(f, expr::Expr)
    for i in 2:length(expr.args)
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

# ReturnNode as terminator is handled in the Block walk, not here.
walk_uses!(f, ::ReturnNode) = nothing

# Nothing terminator
walk_uses!(f, ::Nothing) = nothing


#=============================================================================
 UseIndex: dict-like index mapping values to their use sites
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
 uses(): the public API
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

Find all use sites of `val` in `block` (recursively). This is a linear scan;
for repeated queries, prefer building a `UseIndex` via `uses(block)`.
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
operand. Returns `Instruction` objects, the analog of MLIR's
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
        # `:invoke` callee (args[2]) is a real use; the MI at args[1] is not a
        # value, so start at 2 for both `:invoke` and `:call`.
        for i in 2:length(stmt.args)
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


