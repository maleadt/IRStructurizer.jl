# Structurization helpers: query/collection utilities for control tree → structured IR

using AbstractTrees: PreOrderDFS

#=============================================================================
 Region & Loop Block Helpers
=============================================================================#

"""
    get_region_blocks(tree::ControlTree, ir::IRCode) -> Set{Int}

Get all block indices contained in a control tree region (works for any region type,
including loops).
"""
function get_region_blocks(tree::ControlTree, ir::IRCode)
    blocks = Set{Int}()
    nblocks = length(ir.cfg.blocks)
    for subtree in PreOrderDFS(tree)
        idx = node_index(subtree)
        if 1 <= idx <= nblocks
            push!(blocks, idx)
        end
    end
    return blocks
end

"Alias for `get_region_blocks` — works identically for loop regions."
const get_loop_blocks = get_region_blocks

"""
    compute_natural_loop_blocks(ir::IRCode, header::Int) -> Set{Int}

Compute the natural loop body from the CFG using dominance analysis.
Returns all blocks dominated by the header that are reachable from it
(including unreachable/throw blocks that are internal to the loop).

Unlike `get_loop_blocks` (which uses the control tree and may include exit-target
blocks absorbed by TERMINATION regions), this uses only CFG structure.
"""
function compute_natural_loop_blocks(ir::IRCode, header::Int)
    blocks = ir.cfg.blocks
    nblocks = length(blocks)
    domtree = construct_domtree(ir)

    # Start from the standard natural loop (backward walk from backedge sources)
    loop_blocks = Set{Int}([header])
    worklist = Int[]

    for pred in blocks[header].preds
        (1 <= pred <= nblocks) || continue
        if dominates(domtree, header, pred) && !(pred in loop_blocks)
            push!(loop_blocks, pred)
            push!(worklist, pred)
        end
    end

    while !isempty(worklist)
        block = pop!(worklist)
        for pred in blocks[block].preds
            if !(pred in loop_blocks)
                push!(loop_blocks, pred)
                push!(worklist, pred)
            end
        end
    end

    # Also include dead-end error/throw blocks dominated by the header.
    # These are blocks like bounds-check throws (Union{} return type, no successors)
    # that are internal to the loop but can't reach the backedge source.
    # We do NOT include legitimate exit targets (blocks with return/phi).
    for blk in 1:nblocks
        blk in loop_blocks && continue
        dominates(domtree, header, blk) || continue
        isempty(blocks[blk].succs) || continue
        # Only add if it's an error/throw path (last stmt returns Union{}/Bottom)
        bb = blocks[blk]
        last_type = ir.stmts.type[last(bb.stmts)]
        last_type === Union{} || continue
        any(pred in loop_blocks for pred in bb.preds) || continue
        push!(loop_blocks, blk)
    end

    return loop_blocks
end

"""
    get_exit_block(tree::ControlTree, ir::IRCode) -> Int

Get the exit block index of a control tree region.
For single-block regions, this is the block itself.
For multi-block regions, this is the block that has successors outside the region.
"""
function get_exit_block(tree::ControlTree, ir::IRCode)
    return get_exit_block(tree, ir, get_region_blocks(tree, ir))
end

function get_exit_block(tree::ControlTree, ir::IRCode, blocks::Set{Int})
    nblocks = length(ir.cfg.blocks)

    # Find block(s) with successors outside the region
    for block_idx in blocks
        1 <= block_idx <= nblocks || continue
        for succ in ir.cfg.blocks[block_idx].succs
            if !(succ in blocks)
                return block_idx
            end
        end
    end

    # Fallback to entry block
    return node_index(tree)
end

"""
    convert_phi_value(val) -> IRValue

Convert a phi node value to an IRValue. Most values pass through unchanged;
only QuoteNode needs unwrapping to extract the quoted value.
"""
function convert_phi_value(val)
    val isa QuoteNode ? val.value : val
end

"""
    get_value_type(val, ir::IRCode) -> Type

Get the Julia type of a value that could be SSAValue, SlotNumber, Argument, or a constant.
"""
function get_value_type(val, ir::IRCode)
    if val isa SSAValue
        return widenconst(ir.stmts.type[val.id])
    elseif val isa SlotNumber
        return widenconst(ir.argtypes[val.id])
    elseif val isa Argument
        # Argument(n) maps directly to slottypes[n]
        return widenconst(ir.argtypes[val.n])
    else
        # Constant value
        return typeof(val)
    end
end


"""
    HeaderPhiInfo

Result of extracting phi node information from a loop header.
"""
struct HeaderPhiInfo
    phi_indices::Vector{Int}
    phi_types::Vector{Any}
    init_values::Vector{IRValue}
    carried_values::Vector{IRValue}
end

"""
    extract_header_phis(header_idx, ir, loop_blocks; exclude_iv=nothing) -> HeaderPhiInfo

Extract phi node information from a loop header block. For each phi, determines
the entry value (from outside the loop) and carried value (from inside the loop).

If `exclude_iv` is set, that phi index is included in `phi_indices`/`phi_types`
but excluded from `init_values`/`carried_values` (used for ForOp's induction variable).
"""
function extract_header_phis(header_idx::Int, ir::IRCode, loop_blocks::Set{Int};
                              exclude_iv::Union{Nothing,Int}=nothing)
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    bb = ir.cfg.blocks[header_idx]
    header_range = first(bb.stmts):last(bb.stmts)

    phi_indices = Int[]
    phi_types = Any[]
    init_values = IRValue[]
    carried_values = IRValue[]

    for si in header_range
        stmt = stmts[si]
        stmt isa PhiNode || continue

        push!(phi_indices, si)
        push!(phi_types, types[si])

        entry_val = nothing
        carried_val = nothing
        for (edge_idx, edge) in enumerate(stmt.edges)
            if isassigned(stmt.values, edge_idx)
                val = stmt.values[edge_idx]
                if edge ∈ loop_blocks
                    carried_val = val
                else
                    entry_val = convert_phi_value(val)
                end
            end
        end

        if si != exclude_iv
            entry_val !== nothing && push!(init_values, entry_val)
            carried_val !== nothing && push!(carried_values, carried_val)
        end
    end

    HeaderPhiInfo(phi_indices, phi_types, init_values, carried_values)
end

#=============================================================================
 Statement Collection Helpers
=============================================================================#

"""
    collect_block_statements!(block::Block, block_idx::Int, ir::IRCode;
                               capture_terminator::Bool=true)

Collect statements from a basic block into a Block, excluding control flow
(GotoNode, GotoIfNot, PhiNode). When `capture_terminator=true` (default),
ReturnNode is captured as the block's terminator; when false, ReturnNode is skipped
(used for condition blocks in if-handlers).
"""
function collect_block_statements!(block::Block, block_idx::Int, ir::IRCode;
                                    capture_terminator::Bool=true)
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    nblocks = length(ir.cfg.blocks)
    1 <= block_idx <= nblocks || return
    bb = ir.cfg.blocks[block_idx]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = stmts[si]
        if capture_terminator && stmt isa ReturnNode
            block.terminator = stmt
        elseif !(stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode || stmt isa PhiNode)
            push!(block, si, stmt, types[si])
        end
    end
end

"Emit condition block statements (excludes ReturnNode). Alias for `collect_block_statements!(...; capture_terminator=false)`."
emit_condition_block_stmts!(block::Block, cond_idx::Int, ir::IRCode) =
    collect_block_statements!(block, cond_idx, ir; capture_terminator=false)

"""
    process_child_region!(block::Block, child::ControlTree, ir::IRCode, ctx::StructurizationContext)

Process a control tree child, dispatching to the appropriate handler based on region type.
"""
function process_child_region!(block::Block, child::ControlTree, ir::IRCode,
                                ctx::StructurizationContext)
    if region_type(child) == REGION_BLOCK
        handle_block_region!(block, child, ir, ctx)
    else
        handle_nested_region!(block, child, ir, ctx)
    end
end

"""
    collect_loop_body_stmts!(body::Block, tree::ControlTree, header_idx::Int,
                              ir::IRCode, ctx::StructurizationContext)

Process loop body children (all children except the header) into a body block.
"""
function collect_loop_body_stmts!(body::Block, tree::ControlTree, header_idx::Int,
                                   ir::IRCode, ctx::StructurizationContext)
    for child in children(tree)
        node_index(child) == header_idx && continue
        process_child_region!(body, child, ir, ctx)
    end
end

"""
    find_condition_value(block_idx::Int, ir::IRCode) -> IRValue

Find the condition value for a GotoIfNot in the given block.
"""
function find_condition_value(block_idx::Int, ir::IRCode)
    nblocks = length(ir.cfg.blocks)
    @assert 1 <= block_idx <= nblocks "Invalid block index: $block_idx"

    bb = ir.cfg.blocks[block_idx]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        if stmt isa GotoIfNot
            cond = stmt.cond
            @assert cond isa SSAValue || cond isa SlotNumber || cond isa Argument "Unexpected condition type: $(typeof(cond))"
            return cond
        end
    end

    error("No GotoIfNot found in block $block_idx")
end

"""
    find_condition_chain(stmts, header_range, cond_ssa::SSAValue) -> Set{Int}

Walk backwards from the condition SSA to find all SSA indices in the header
that contribute to computing the condition. These should be excluded from
the ForOp body since they're part of the loop control, not the loop body.
"""
function find_condition_chain(stmts, header_range, cond_ssa::SSAValue)
    chain = Set{Int}()
    worklist = [cond_ssa.id]
    while !isempty(worklist)
        idx = popfirst!(worklist)
        idx in header_range || continue
        idx in chain && continue
        push!(chain, idx)
        # Add operands that are SSAValues in header
        stmt = stmts[idx]
        if stmt isa Expr
            for arg in stmt.args
                if arg isa SSAValue && arg.id in header_range
                    push!(worklist, arg.id)
                end
            end
        end
    end
    return chain
end

"""
    set_block_terminator!(block::Block, ir::IRCode)

Set the block terminator based on statements.
"""
function set_block_terminator!(block::Block, ir::IRCode)
    block.terminator !== nothing && return

    last_idx = nothing
    for (idx, entry) in block.body
        if !(entry.stmt isa ControlFlowOp)
            if last_idx === nothing || idx > last_idx
                last_idx = idx
            end
        end
    end
    if last_idx !== nothing && last_idx < length(ir.stmts.stmt)
        next_stmt = ir.stmts.stmt[last_idx + 1]
        if next_stmt isa ReturnNode
            block.terminator = next_stmt
        end
    end
end
