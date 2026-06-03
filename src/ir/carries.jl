#=============================================================================
 Loop carries abstraction
=============================================================================#

export carries, init_value, body_arg, term_value, init_value!, term_value!

const LoopOps = Union{ForOp, LoopOp, WhileOp}

"""
    LoopCarries(op::Union{ForOp, LoopOp, WhileOp})

View over a loop op's carried values. Encapsulates the positional coupling
between init_values, body args, and terminator values.

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
        new_block_arg!(op.after, body_arg_type)
    end

    return CarryRef(carries, length(op.init_values))
end


