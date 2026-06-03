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

    # Outer terminator. Include yield/condition here because outer may be an IfOp.
    let
        term = outer.terminator
        if term isa ContinueOp || term isa BreakOp || term isa YieldOp || term isa ConditionOp
            push!(result, term)
        end
    end

    # Nested terminators reachable through nested IfOps. Ignore yield/condition
    # here because those are inner to the IfOp.
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
 walk: operation/block walker with control flow (cf. MLIR walk())
=============================================================================#

"""
    walk(f, root::Union{Block, StructuredIRCode}; order=:preorder)

Walk all instructions, calling `f(inst, block)` for each. The callback
returns a `Symbol` controlling traversal:

- `:advance`: continue normally (default if callback returns `nothing`)
- `:skip`: do not recurse into this op's sub-blocks (only meaningful for `ControlFlowOp`s)
- `:interrupt`: stop the walk immediately

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


