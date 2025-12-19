# loop helper functions for restructuring.jl
#
# These functions are used by the two-phase restructuring approach:
# - Phase 1 uses get_loop_blocks, convert_phi_value
# - Phase 2 uses pattern matching helpers on structured IR

#=============================================================================
 Phase 1 Helper Functions (CFG analysis)
=============================================================================#

"""
    get_loop_blocks(tree::ControlTree, blocks::Vector{BlockInfo}) -> Set{Int}

Get all block indices contained in a loop control tree.
"""
function get_loop_blocks(tree::ControlTree, blocks::Vector{BlockInfo})
    loop_blocks = Set{Int}()
    for subtree in PreOrderDFS(tree)
        idx = node_index(subtree)
        if 1 <= idx <= length(blocks)
            push!(loop_blocks, idx)
        end
    end
    return loop_blocks
end

"""
    convert_phi_value(val) -> IRValue

Convert a phi node value to an IRValue.
"""
function convert_phi_value(val)
    if val isa SSAValue
        return val
    elseif val isa Argument
        return val
    elseif val isa Integer
        return val
    elseif val isa QuoteNode
        return val.value
    else
        return 0  # Fallback
    end
end

#=============================================================================
 Phase 2 Helper Functions (Pattern matching on structured IR)
=============================================================================#

"""
    find_ifop(block::Block) -> Union{IfOp, Nothing}

Find the first IfOp in a block's body.
"""
function find_ifop(block::Block)
    for item in block.body
        if item isa IfOp
            return item
        end
    end
    return nothing
end

"""
    find_statement_by_ssa(block::Block, ssa::SSAValue) -> Union{Statement, Nothing}

Find a Statement in the block whose idx matches the SSAValue's id.
"""
function find_statement_by_ssa(block::Block, ssa::SSAValue)
    for item in block.body
        if item isa Statement && item.idx == ssa.id
            return item
        end
    end
    return nothing
end

"""
    find_add_int_for_iv(block::Block, iv_arg::BlockArg) -> Union{Statement, Nothing}

Find a Statement containing `add_int(iv_arg, step)` in the block.
Searches inside IfOp blocks (since condition creates IfOp structure),
but NOT into nested LoopOps (those have their own IVs).
"""
function find_add_int_for_iv(block::Block, iv_arg::BlockArg)
    for item in block.body
        if item isa Statement
            expr = item.expr
            if expr isa Expr && expr.head === :call && length(expr.args) >= 3
                func = expr.args[1]
                if func isa GlobalRef && func.name === :add_int
                    if expr.args[2] == iv_arg
                        return item
                    end
                end
            end
        elseif item isa IfOp
            # Search in IfOp blocks (condition structure)
            result = find_add_int_for_iv(item.then_block, iv_arg)
            result !== nothing && return result
            result = find_add_int_for_iv(item.else_block, iv_arg)
            result !== nothing && return result
        end
        # Don't recurse into LoopOp - nested loops have their own IVs
    end
    return nothing
end

"""
    is_loop_invariant(val, block::Block) -> Bool

Check if a value is loop-invariant (not defined inside the loop body).
- BlockArgs are loop-variant (they're loop-carried values)
- SSAValues are loop-invariant if no Statement in the body defines them
- Constants and Arguments are always loop-invariant
"""
function is_loop_invariant(val, block::Block)
    # BlockArgs are loop-carried values - not invariant
    val isa BlockArg && return false

    # SSAValues: check if defined in the loop body (including nested blocks)
    if val isa SSAValue
        return !defines(block, val)
    end

    # Constants, Arguments, etc. are invariant
    return true
end

"""
    defines(block::Block, ssa::SSAValue) -> Bool

Check if a block defines an SSA value (i.e., contains a Statement that produces it).
Searches nested blocks recursively.
"""
function defines(block::Block, ssa::SSAValue)
    for item in block.body
        if item isa Statement && item.idx == ssa.id
            return true
        elseif item isa IfOp
            defines(item.then_block, ssa) && return true
            defines(item.else_block, ssa) && return true
        elseif item isa LoopOp
            defines(item.body, ssa) && return true
        end
    end
    return false
end

"""
    is_for_condition(expr) -> Bool

Check if an expression is a for-loop condition pattern: slt_int or ult_int.
"""
function is_for_condition(expr)
    expr isa Expr || return false
    expr.head === :call || return false
    length(expr.args) >= 3 || return false
    func = expr.args[1]
    return func isa GlobalRef && func.name in (:slt_int, :ult_int)
end
