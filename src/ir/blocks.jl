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
the per-statement `IR_FLAG_*` bitmask (defaults to 0 / `IR_FLAG_NULL`). It is
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
 Statement access: Symbol-keyed on Instruction, NamedTuple-keyed on Block

 Modeled on Core.Compiler.Instruction (`Compiler/src/ssair/ir.jl`): each
 `Instruction` is a thin handle, and reads/writes resolve to the live
 SSAMap entry on every access.

 When swapping a stmt for one with a different opcode, the old `flag` bits
 describe the old op and may be stale for the new one. Pass `flag=IR_FLAG_NULL`
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

This is the widened-type view over [`argextype`](@ref); call `const_value` for
the static value when known.
"""
function value_type(block::Block, @nospecialize(val))
    lat = argextype(block, val)
    lat === nothing && return nothing
    return widenconst(lat)
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


