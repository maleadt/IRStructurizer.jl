# loop helper functions for restructuring.jl
#
# These functions are used by the two-phase restructuring approach:
# - Phase 1 uses get_loop_blocks, convert_phi_value, is_value_in_loop
# - Phase 2 uses these same helpers for pattern detection

#=============================================================================
 Helper Functions
=============================================================================#

"""
    is_value_in_loop(val, stmts, stmt_to_blk, loop_blocks) -> Bool

Check if a value originates from inside the loop.
"""
function is_value_in_loop(val, stmts, stmt_to_blk, loop_blocks)
    if val isa SSAValue && val.id > 0 && val.id <= length(stmts)
        return stmt_to_blk[val.id] ∈ loop_blocks
    end
    return false
end

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
