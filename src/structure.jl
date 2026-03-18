# Control Tree to Structured IR

using AbstractTrees: PreOrderDFS

#=============================================================================
 Helpers
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
        return ir.stmts.type[val.id]
    elseif val isa SlotNumber
        return ir.argtypes[val.id]
    elseif val isa Argument
        # Argument(n) maps directly to slottypes[n]
        return ir.argtypes[val.n]
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
 Control Tree to Structured IR
=============================================================================#

"""
    control_tree_to_structured_ir(ctree::ControlTree, ir::IRCode, ctx::StructurizationContext) -> Block

Convert a control tree to structured IR entry block.
All loops become LoopOp (no pattern matching yet, no substitutions).
"""
function control_tree_to_structured_ir(ctree::ControlTree, ir::IRCode,
                                       ctx::StructurizationContext)
    return tree_to_block(ctree, ir, ctx)
end

"""
    tree_to_block(tree::ControlTree, ir::IRCode, ctx::StructurizationContext) -> Block

Convert a control tree node to a Block with raw expressions (no substitutions).
"""
function tree_to_block(tree::ControlTree, ir::IRCode, ctx::StructurizationContext)
    idx = node_index(tree)
    rtype = region_type(tree)
    block = Block()

    if rtype == REGION_BLOCK
        handle_block_region!(block, tree, ir, ctx)
    elseif rtype == REGION_IF_THEN_ELSE
        handle_if_then_else!(block, tree, ir, ctx)
    elseif rtype == REGION_IF_THEN
        handle_if_then!(block, tree, ir, ctx)
    elseif rtype == REGION_TERMINATION
        handle_termination!(block, tree, ir, ctx)
    elseif rtype == REGION_FOR_LOOP || rtype == REGION_WHILE_LOOP || rtype == REGION_NATURAL_LOOP
        handle_loop!(block, tree, ir, ctx)
    elseif rtype == REGION_PROPER
        handle_proper_region!(block, tree, ir, ctx)
    else
        error("Unknown region type: $rtype")
    end

    # Set terminator if not already set
    set_block_terminator!(block, ir)

    return block
end

#=============================================================================
 Region Handlers
=============================================================================#

"""
    handle_block_region!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_BLOCK - a linear sequence of blocks.
"""
function handle_block_region!(block::Block, tree::ControlTree, ir::IRCode,
                              ctx::StructurizationContext)
    nblocks = length(ir.cfg.blocks)
    if isempty(children(tree))
        # Leaf node - collect statements from the block
        idx = node_index(tree)
        if 1 <= idx <= nblocks
            collect_block_statements!(block, idx, ir)
        end
    else
        # Non-leaf - process children in order
        for child in children(tree)
            child_rtype = region_type(child)
            if child_rtype == REGION_BLOCK
                handle_block_region!(block, child, ir, ctx)
            else
                # Nested control flow - create appropriate op
                handle_nested_region!(block, child, ir, ctx)
            end
        end
    end
end

"""
    handle_nested_region!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle a nested control flow region.
"""
function handle_nested_region!(block::Block, tree::ControlTree, ir::IRCode,
                               ctx::StructurizationContext)
    rtype = region_type(tree)

    if rtype == REGION_IF_THEN_ELSE
        handle_if_then_else!(block, tree, ir, ctx)
    elseif rtype == REGION_IF_THEN
        handle_if_then!(block, tree, ir, ctx)
    elseif rtype == REGION_TERMINATION
        handle_termination!(block, tree, ir, ctx)
    elseif rtype == REGION_FOR_LOOP || rtype == REGION_WHILE_LOOP || rtype == REGION_NATURAL_LOOP
        handle_loop!(block, tree, ir, ctx)
    elseif rtype == REGION_PROPER
        handle_proper_region!(block, tree, ir, ctx)
    else
        error("Unknown region type in nested region: $rtype")
    end
end

"""
    resolve_yield(blk, phi_ssa_idx, default_val)

If `blk` already defines `phi_ssa_idx` (e.g., via an inner IfOp's getfield for nested
short-circuit patterns), yield SSAValue(phi_ssa_idx). Otherwise yield `default_val`.
"""
function resolve_yield(blk::Block, phi_ssa_idx::Int, default_val)
    get(blk.body, phi_ssa_idx, nothing) !== nothing ? SSAValue(phi_ssa_idx) : default_val
end

"""
    emit_ifop_result!(block, if_op, phi_ssa_indices, phi_types, ctx) -> Int

Push an IfOp to `block` with its result type, then generate getfield statements at
each `phi_ssa_indices[i]`. Returns the IfOp's SSA index.

Used by `emit_if_op!`, `handle_proper_region!`, and `build_proper_branch!` to avoid
repeating the IfOp allocation / getfield pattern.
"""
function emit_ifop_result!(block::Block, if_op::IfOp, phi_ssa_indices::Vector{Int},
                            phi_types::Vector{Any}, ctx::StructurizationContext)
    if_result_idx = ctx.next_ssa_idx
    ctx.next_ssa_idx += 1

    if !isempty(phi_ssa_indices)
        result_type = Tuple{phi_types...}
        push!(block, if_result_idx, if_op, result_type)

        for (i, (phi_idx, phi_type)) in enumerate(zip(phi_ssa_indices, phi_types))
            getfield_expr = Expr(:call, Core.getfield, SSAValue(if_result_idx), i)
            push!(block, phi_idx, getfield_expr, phi_type)
        end
    else
        push!(block, if_result_idx, if_op, Tuple{})
    end

    return if_result_idx
end

"""
    emit_if_op!(block, cond_idx, then_tree, else_tree_or_nothing, ir, ctx; is_termination=false)

Unified handler for if-like regions (IF_THEN_ELSE, IF_THEN, TERMINATION).

- For IF_THEN_ELSE: pass both then_tree and else_tree
- For IF_THEN: pass else_tree=nothing (creates empty else block, uses cond_idx as else proxy)
- For TERMINATION: pass is_termination=true (preserves return terminators, Nothing result type)
"""
function emit_if_op!(block::Block, cond_idx::Int,
                      then_tree::ControlTree, else_tree::Union{ControlTree,Nothing},
                      ir::IRCode, ctx::StructurizationContext;
                      is_termination::Bool=false)
    emit_condition_block_stmts!(block, cond_idx, ir)
    cond_value = find_condition_value(cond_idx, ir)

    then_blk = tree_to_block(then_tree, ir, ctx)
    else_blk = else_tree !== nothing ? tree_to_block(else_tree, ir, ctx) : Block()

    if is_termination
        then_blk.terminator = something(then_blk.terminator, YieldOp())
        else_blk.terminator = something(else_blk.terminator, YieldOp())
        if_op = IfOp(cond_value, then_blk, else_blk)

        # Use gotoifnot SSA index as result key
        nblocks = length(ir.cfg.blocks)
        bb = ir.cfg.blocks[cond_idx]
        result_idx = last(bb.stmts)
        for si in first(bb.stmts):last(bb.stmts)
            ir.stmts.stmt[si] isa GotoIfNot && (result_idx = si; break)
        end
        push!(block, result_idx, if_op, Nothing)
    else
        # Find merge phis
        then_rblocks = get_region_blocks(then_tree, ir)
        then_exit = get_exit_block(then_tree, ir, then_rblocks)

        else_rblocks = else_tree !== nothing ?
            get_region_blocks(else_tree, ir) : Set{Int}((cond_idx,))
        else_exit = else_tree !== nothing ?
            get_exit_block(else_tree, ir, else_rblocks) : cond_idx

        merge_phis = find_merge_phis(ir, then_exit, else_exit;
                                      then_blocks=then_rblocks,
                                      else_blocks=else_rblocks)

        then_blk.terminator, else_blk.terminator = if !isempty(merge_phis)
            # If a branch already defines the merge phi's SSA index (e.g., via an inner
            # IfOp's getfield for nested short-circuit patterns like &&), yield that
            # SSAValue instead of the raw phi edge value from find_merge_phis.
            YieldOp([resolve_yield(then_blk, phi.ssa_idx, phi.then_val) for phi in merge_phis]),
            YieldOp([resolve_yield(else_blk, phi.ssa_idx, phi.else_val) for phi in merge_phis])
        else
            something(then_blk.terminator, YieldOp()),
            something(else_blk.terminator, YieldOp())
        end

        if_op = IfOp(cond_value, then_blk, else_blk)
        phi_indices = Int[phi.ssa_idx for phi in merge_phis]
        phi_types = Any[ctx.ssavaluetypes[phi.ssa_idx] for phi in merge_phis]
        emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx)
    end
end

"""
    handle_if_then_else!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_IF_THEN_ELSE.
"""
function handle_if_then_else!(block::Block, tree::ControlTree, ir::IRCode,
                              ctx::StructurizationContext)
    tree_children = children(tree)
    length(tree_children) >= 3 || return handle_block_region!(block, tree, ir, ctx)
    cond_idx = node_index(tree_children[1])
    emit_if_op!(block, cond_idx, tree_children[2], tree_children[3], ir, ctx)
end

"""
    is_defined_in_blocks(val, blocks::Set{Int}, ir::IRCode) -> Bool

Check if an SSAValue's definition falls within any of the given blocks' stmt ranges.
Non-SSAValue values (constants, Arguments) are always considered "not block-local".
"""
function is_defined_in_blocks(val, blocks::Set{Int}, ir::IRCode)
    val isa SSAValue || return false
    nblocks = length(ir.cfg.blocks)
    for block_idx in blocks
        1 <= block_idx <= nblocks || continue
        bb = ir.cfg.blocks[block_idx]
        if val.id in first(bb.stmts):last(bb.stmts)
            return true
        end
    end
    return false
end

"""
    find_extra_exit_values(ir, exit_dest, loop_blocks, already_exported) -> Vector{NamedTuple}

Find loop-internal values referenced in the exit target block that are not already
exported via header phis. Returns a vector of `(; value, getfield_idx, type)` tuples.

Scans both PhiNodes (with edges from loop blocks) and non-phi statements whose
Expr arguments are SSAValues defined inside the loop.
"""
function find_extra_exit_values(ir::IRCode, exit_dest::Int, loop_blocks::Set{Int},
                                already_exported::Set{Int})
    extra = @NamedTuple{value::IRValue, getfield_idx::Int, type::Any}[]
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    nblocks = length(ir.cfg.blocks)
    1 <= exit_dest <= nblocks || return extra

    exit_bb = ir.cfg.blocks[exit_dest]
    seen = Set{Int}()  # track getfield_idx to avoid duplicates

    for si in first(exit_bb.stmts):last(exit_bb.stmts)
        stmt = stmts[si]

        if stmt isa PhiNode
            si ∈ already_exported && continue

            # Find value from loop blocks
            loop_val = nothing
            for (edge_idx, edge) in enumerate(stmt.edges)
                if isassigned(stmt.values, edge_idx) && edge ∈ loop_blocks
                    loop_val = stmt.values[edge_idx]
                end
            end

            if loop_val !== nothing
                gf_idx = loop_val isa SSAValue ? loop_val.id : si
                push!(extra, (; value=loop_val, getfield_idx=gf_idx, type=types[si]))
                push!(seen, gf_idx)
            end
        else
            # Non-phi statement: check if any Expr arg is an SSAValue defined in loop blocks
            stmt isa Expr || continue
            for arg in stmt.args
                if arg isa SSAValue && is_defined_in_blocks(arg, loop_blocks, ir)
                    arg.id ∈ already_exported && continue
                    arg.id ∈ seen && continue
                    push!(extra, (; value=arg, getfield_idx=arg.id, type=types[arg.id]))
                    push!(seen, arg.id)
                end
            end
        end
    end

    return extra
end

"""
    pad_extra_exits!(extra_exits, init_values, carried_values, body, phi_indices, phi_types, arg_offset)

Pad extra exit values into the loop-carry chain and append to phi tracking vectors.
Each extra exit value becomes a loop-carried variable with `Undef` initial value.
`arg_offset` is the starting BlockArg id for the new args.
"""
function pad_extra_exits!(extra_exits, init_values, carried_values, body, phi_indices, phi_types, arg_offset::Int)
    for (j, ex) in enumerate(extra_exits)
        push!(init_values, Undef(ex.type))
        push!(carried_values, ex.value)
        push!(body.args, BlockArg(arg_offset + j, ex.type))
    end
    for ex in extra_exits
        push!(phi_indices, ex.getfield_idx)
        push!(phi_types, ex.type)
    end
end

"""
    find_merge_phis(ir, then_block_idx, else_block_idx; then_blocks, else_blocks)

Find phis in the merge block (common successor of then and else blocks)
that receive values from both branches.

When a phi has only one incoming edge and the value is branch-local (defined
within that branch's blocks), `Undef(T)` is used for the dead branch instead
of duplicating the branch-local SSAValue.

Returns a vector of NamedTuples: (ssa_idx, then_val, else_val)
"""
function find_merge_phis(ir::IRCode, then_block_idx::Int, else_block_idx::Int;
                         then_blocks::Set{Int}=Set{Int}(), else_blocks::Set{Int}=Set{Int}())
    merge_phis = NamedTuple{(:ssa_idx, :then_val, :else_val), Tuple{Int, Any, Any}}[]
    nblocks = length(ir.cfg.blocks)

    # Find common successor (merge block)
    then_succs = 1 <= then_block_idx <= nblocks ? ir.cfg.blocks[then_block_idx].succs : Int[]
    else_succs = 1 <= else_block_idx <= nblocks ? ir.cfg.blocks[else_block_idx].succs : Int[]
    merge_blocks = intersect(then_succs, else_succs)
    isempty(merge_blocks) && return merge_phis

    merge_block_idx = first(merge_blocks)
    1 <= merge_block_idx <= nblocks || return merge_phis
    merge_bb = ir.cfg.blocks[merge_block_idx]

    # Look for phis that have edges from both then and else blocks
    # In IRCode, phi edges are BLOCK indices directly
    for si in first(merge_bb.stmts):last(merge_bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa PhiNode || continue

        then_val = nothing
        else_val = nothing
        for (edge_idx, edge) in enumerate(stmt.edges)
            # edge is a block index in IRCode
            if edge == then_block_idx
                then_val = stmt.values[edge_idx]
            elseif edge == else_block_idx
                else_val = stmt.values[edge_idx]
            end
        end

        # Include phis with values from at least one branch.
        # In SSA form, a phi with only one incoming edge means the value is live on that
        # path alone. A structured IfOp must yield equal arity from both branches.
        if then_val !== nothing && else_val !== nothing
            push!(merge_phis, (ssa_idx=si, then_val=then_val, else_val=else_val))
        elseif then_val !== nothing
            # Only then branch has a value. If branch-local, the other path gets Undef
            # (the value is dead there, guarded by the branch condition).
            if is_defined_in_blocks(then_val, then_blocks, ir)
                push!(merge_phis, (ssa_idx=si, then_val=then_val, else_val=Undef(ir.stmts.type[si])))
            else
                # Value is visible in both scopes (e.g., Argument, constant, or outer SSA)
                push!(merge_phis, (ssa_idx=si, then_val=then_val, else_val=then_val))
            end
        elseif else_val !== nothing
            if is_defined_in_blocks(else_val, else_blocks, ir)
                push!(merge_phis, (ssa_idx=si, then_val=Undef(ir.stmts.type[si]), else_val=else_val))
            else
                push!(merge_phis, (ssa_idx=si, then_val=else_val, else_val=else_val))
            end
        end
    end

    return merge_phis
end

"""
    handle_if_then!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_IF_THEN.
"""
function handle_if_then!(block::Block, tree::ControlTree, ir::IRCode,
                         ctx::StructurizationContext)
    tree_children = children(tree)
    length(tree_children) >= 2 || return handle_block_region!(block, tree, ir, ctx)
    cond_idx = node_index(tree_children[1])
    emit_if_op!(block, cond_idx, tree_children[2], nothing, ir, ctx)
end

"""
    handle_termination!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_TERMINATION - branches where some paths terminate.
"""
function handle_termination!(block::Block, tree::ControlTree, ir::IRCode,
                             ctx::StructurizationContext)
    tree_children = children(tree)
    isempty(tree_children) && return handle_block_region!(block, tree, ir, ctx)
    cond_idx = node_index(tree_children[1])

    if length(tree_children) >= 3
        emit_if_op!(block, cond_idx, tree_children[2], tree_children[3], ir, ctx;
                     is_termination=true)
    elseif length(tree_children) == 2
        emit_if_op!(block, cond_idx, tree_children[2], nothing, ir, ctx;
                     is_termination=true)
    end
end

"""
    handle_loop!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_FOR_LOOP, REGION_WHILE_LOOP, and REGION_NATURAL_LOOP.

For REGION_FOR_LOOP: Creates ForOp directly using metadata from CFG analysis.
For REGION_WHILE_LOOP: Creates WhileOp directly with before/after regions.
For REGION_NATURAL_LOOP: Creates LoopOp with internal IfOp (fallback for complex loops).

The loop is keyed at a synthesized SSA index, and getfield statements are generated
at the original phi node indices. This ensures that references like `return %2`
continue to work because getfield is placed at %2.
"""
function handle_loop!(block::Block, tree::ControlTree, ir::IRCode,
                      ctx::StructurizationContext)
    rtype = region_type(tree)

    # Dispatch based on region type
    post_loop_blocks = Int[]
    if rtype == REGION_FOR_LOOP
        loop_op, phi_indices, phi_types = build_for_op(block, tree, ir, ctx)
    elseif rtype == REGION_WHILE_LOOP
        loop_op, phi_indices, phi_types = build_while_op(tree, ir, ctx)
    else  # REGION_NATURAL_LOOP or other cyclic regions
        loop_op, phi_indices, phi_types, post_loop_blocks = build_loop_op(tree, ir, ctx)
    end

    # Allocate new SSA index for loop's tuple result
    loop_result_idx = ctx.next_ssa_idx
    ctx.next_ssa_idx += 1

    # Always use Tuple type for loop results (uniform handling in codegen)
    # Empty phi_indices produces Tuple{} which is fine
    result_type = Tuple{phi_types...}

    # Push loop op at synthesized index
    push!(block, loop_result_idx, loop_op, result_type)

    # Generate getfield statements at original phi indices
    # This preserves SSA reference semantics: `return %2` still works because getfield is at %2
    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
        getfield_expr = Expr(:call, Core.getfield, SSAValue(loop_result_idx), i)
        push!(block, phi_idx, getfield_expr, phi_type)
    end

    # For ForOp, the IV phi is excluded from phi_indices but may still be referenced.
    # Define it as the exclusive upper bound (the IV's value at loop exit).
    if rtype == REGION_FOR_LOOP
        for_info = metadata(tree)::ForLoopInfo
        iv_phi_idx = for_info.iv_phi_idx
        iv_type = ctx.ssavaluetypes[iv_phi_idx]
        push!(block, iv_phi_idx, loop_op.upper, iv_type)
    end

    # Emit post-loop content: blocks that were in the control tree but outside
    # the natural loop (e.g., exit-target blocks absorbed by TERMINATION regions).
    for blk_idx in post_loop_blocks
        collect_block_statements!(block, blk_idx, ir)
    end
end

"""
    handle_proper_region!(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)

Handle REGION_PROPER — a multi-exit acyclic region (e.g., short-circuit `||`/`&&`).

Lowers to nested IfOps by tracing each path from entry to the merge block.
The merge block may be inside the region (e.g., `||`) or outside it (e.g., `&&`);
both cases are handled.
"""
function handle_proper_region!(block::Block, tree::ControlTree, ir::IRCode,
                                ctx::StructurizationContext)
    tree_children = children(tree)
    isempty(tree_children) && return handle_block_region!(block, tree, ir, ctx)

    nblocks = length(ir.cfg.blocks)
    entry_idx = node_index(tree_children[1])
    1 <= entry_idx <= nblocks || return handle_block_region!(block, tree, ir, ctx)

    # Verify entry block has a GotoIfNot
    bb = ir.cfg.blocks[entry_idx]
    gotoifnot = nothing
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa GotoIfNot && (gotoifnot = stmt; break)
    end
    gotoifnot === nothing && return handle_block_region!(block, tree, ir, ctx)

    region_blocks = get_region_blocks(tree, ir)

    # Find merge block: a block with phi nodes having ≥2 edges from region blocks.
    # Try inside the region first (e.g., `||`), then outside (e.g., `&&`).
    merge_idx = find_proper_merge_block(region_blocks, ir, nblocks)
    merge_idx === nothing && return handle_block_region!(block, tree, ir, ctx)
    merge_is_internal = merge_idx in region_blocks

    # Collect merge phi information: for each phi, map predecessor block → value
    merge_phis = collect_proper_merge_phis(merge_idx, region_blocks, ir)

    # Emit entry block statements (excluding control flow and phis)
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        if !(stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode || stmt isa PhiNode)
            push!(block, si, stmt, ir.stmts.type[si])
        end
    end

    cond_value = find_condition_value(entry_idx, ir)

    # GotoIfNot: condition false → dest, condition true → fallthrough
    false_target = gotoifnot.dest
    true_target = nothing
    for succ in ir.cfg.blocks[entry_idx].succs
        succ != false_target && (true_target = succ; break)
    end

    # Build mapping from block index → control tree child for non-leaf sub-trees.
    # When build_proper_branch! encounters such a block, it processes the sub-tree
    # via tree_to_block instead of walking raw IR blocks.
    subtree_map = Dict{Int, ControlTree}()
    for child in tree_children
        if !isempty(children(child))
            subtree_map[node_index(child)] = child
        end
    end

    # Build then and else branches recursively
    then_blk = Block()
    else_blk = Block()
    build_proper_branch!(then_blk, true_target, entry_idx, merge_idx, merge_phis,
                          region_blocks, ir, ctx, subtree_map)
    build_proper_branch!(else_blk, false_target, entry_idx, merge_idx, merge_phis,
                          region_blocks, ir, ctx, subtree_map)

    # Emit IfOp with merge phi results
    if_op = IfOp(cond_value, then_blk, else_blk)
    phi_indices = Int[phi.ssa_idx for phi in merge_phis]
    phi_types = Any[ctx.ssavaluetypes[phi.ssa_idx] for phi in merge_phis]
    emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx)

    # If merge block is inside the region, process its non-phi statements here
    if merge_is_internal
        merge_bb = ir.cfg.blocks[merge_idx]
        for si in first(merge_bb.stmts):last(merge_bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa ReturnNode
                block.terminator = stmt
            elseif !(stmt isa PhiNode || stmt isa GotoNode || stmt isa GotoIfNot)
                push!(block, si, stmt, ir.stmts.type[si])
            end
        end
    end
end

"""
    find_proper_merge_block(region_blocks, ir, nblocks) -> Union{Int, Nothing}

Find the merge block for a proper region: a block with phi nodes having ≥2 edges
from region blocks. Searches both inside (e.g., `||`) and outside (e.g., `&&`).
"""
function find_proper_merge_block(region_blocks::Set{Int}, ir::IRCode, nblocks::Int)
    # Collect candidates: internal blocks (reverse-sorted, merge is typically last in RPO)
    # plus external successor blocks.
    candidates = sort!(collect(region_blocks); rev=true)
    for b in region_blocks
        1 <= b <= nblocks || continue
        for succ in ir.cfg.blocks[b].succs
            succ in region_blocks || push!(candidates, succ)
        end
    end

    # Single pass: find first block with a phi having ≥2 edges from region blocks
    for idx in candidates
        1 <= idx <= nblocks || continue
        bb = ir.cfg.blocks[idx]
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa PhiNode
                region_edge_count = count(e -> e in region_blocks, stmt.edges)
                region_edge_count >= 2 && return idx
            end
        end
    end

    return nothing
end

"""
    collect_proper_merge_phis(merge_idx, region_blocks, ir)

Collect phi nodes from a merge block that have edges from within the region.
Returns a vector of (ssa_idx, edge_values) named tuples.
"""
function collect_proper_merge_phis(merge_idx::Int, region_blocks::Set{Int}, ir::IRCode)
    merge_phis = @NamedTuple{ssa_idx::Int, edge_values::Dict{Int,Any}}[]
    merge_bb = ir.cfg.blocks[merge_idx]
    for si in first(merge_bb.stmts):last(merge_bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa PhiNode || continue
        edge_values = Dict{Int,Any}()
        for (edge_idx, edge) in enumerate(stmt.edges)
            if isassigned(stmt.values, edge_idx) && edge in region_blocks
                edge_values[edge] = stmt.values[edge_idx]
            end
        end
        isempty(edge_values) || push!(merge_phis, (ssa_idx=si, edge_values=edge_values))
    end
    return merge_phis
end

"""
    build_proper_branch!(branch_blk, target, from_block, merge_idx, merge_phis,
                          region_blocks, ir, ctx, subtree_map)

Build a branch block for a proper region by following the path from `target` to the
merge block, creating nested IfOps at branch points.

`from_block` is the block that branches to `target` (needed for merge phi lookup
when the target goes directly to the merge).

`subtree_map` maps block indices to their control tree sub-trees; when the path
encounters such a block, the sub-tree is processed via `tree_to_block` instead of
walking raw IR blocks (needed for nested patterns like `||` with `&&`).
"""
function build_proper_branch!(branch_blk::Block, target::Union{Int,Nothing},
                               from_block::Int, merge_idx::Int,
                               merge_phis,
                               region_blocks::Set{Int},
                               ir::IRCode, ctx::StructurizationContext,
                               subtree_map::Dict{Int, ControlTree}=Dict{Int, ControlTree}())
    nblocks = length(ir.cfg.blocks)

    # If target is the merge or outside region, yield merge phi values
    if target === nothing || target == merge_idx ||
       !(target in region_blocks) || !(1 <= target <= nblocks)
        branch_blk.terminator = yield_for_merge_edge(from_block, merge_phis, ctx)
        return
    end

    # Walk the path from target, emitting statements
    current = target
    while true
        # Check if current block is the root of a control tree sub-tree.
        # If so, process via tree_to_block (handles internal phis, IfOps, etc.)
        subtree = get(subtree_map, current, nothing)
        if subtree !== nothing
            sub_block = tree_to_block(subtree, ir, ctx)
            # Merge sub-tree results into branch_blk
            for (idx, entry) in sub_block.body
                push!(branch_blk, idx, entry.stmt, entry.typ)
            end
            # Find the exit successor of the sub-tree (next block on the path)
            sub_blocks = get_region_blocks(subtree, ir)
            next = nothing
            for b in sub_blocks
                1 <= b <= nblocks || continue
                for succ in ir.cfg.blocks[b].succs
                    if !(succ in sub_blocks) && (succ in region_blocks || succ == merge_idx)
                        next = succ
                        break
                    end
                end
                next !== nothing && break
            end
            if next === nothing || next == merge_idx
                # Sub-tree exits to merge
                exit_idx = get_exit_block(subtree, ir, sub_blocks)
                branch_blk.terminator = yield_for_merge_edge(exit_idx, merge_phis, ctx)
                return
            end
            current = next
            continue
        end

        bb = ir.cfg.blocks[current]

        # Emit non-control-flow statements (skip phis — they may have been
        # resolved by a preceding sub-tree's getfield at the same SSA index)
        gotoifnot = nothing
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa GotoIfNot
                gotoifnot = stmt
            elseif !(stmt isa GotoNode || stmt isa ReturnNode || stmt isa PhiNode)
                push!(branch_blk, si, stmt, ir.stmts.type[si])
            end
        end

        if gotoifnot !== nothing
            # Nested branch — create inner IfOp
            cond_value = find_condition_value(current, ir)
            false_target = gotoifnot.dest
            true_target = nothing
            for succ in ir.cfg.blocks[current].succs
                succ != false_target && (true_target = succ; break)
            end

            then_inner = Block()
            else_inner = Block()
            build_proper_branch!(then_inner, true_target, current, merge_idx,
                                  merge_phis, region_blocks, ir, ctx, subtree_map)
            build_proper_branch!(else_inner, false_target, current, merge_idx,
                                  merge_phis, region_blocks, ir, ctx, subtree_map)

            inner_if = IfOp(cond_value, then_inner, else_inner)

            # Use synthesized SSA indices for getfield (these are intermediate
            # results inside a branch, not the final merge phi indices)
            phi_types = Any[ctx.ssavaluetypes[phi.ssa_idx] for phi in merge_phis]
            gf_indices = Int[]
            for _ in merge_phis
                push!(gf_indices, ctx.next_ssa_idx)
                ctx.next_ssa_idx += 1
            end
            emit_ifop_result!(branch_blk, inner_if, gf_indices, phi_types, ctx)
            branch_blk.terminator = if !isempty(gf_indices)
                YieldOp(IRValue[SSAValue(idx) for idx in gf_indices])
            else
                YieldOp()
            end
            return
        end

        # No branch — follow to next block
        next = nothing
        for succ in ir.cfg.blocks[current].succs
            next = succ
            break
        end

        if next === nothing || next == merge_idx
            # Reached merge
            branch_blk.terminator = yield_for_merge_edge(current, merge_phis, ctx)
            return
        end

        if !(next in region_blocks) || !(1 <= next <= nblocks)
            # Exited region (shouldn't normally happen)
            branch_blk.terminator = yield_for_merge_edge(current, merge_phis, ctx)
            return
        end

        current = next
    end
end

"""
    yield_for_merge_edge(pred_block, merge_phis, ctx) -> YieldOp

Create a YieldOp with values from the merge phis for the given predecessor edge.
"""
function yield_for_merge_edge(pred_block::Int, merge_phis, ctx::StructurizationContext)
    yield_values = IRValue[]
    for phi in merge_phis
        val = get(phi.edge_values, pred_block, nothing)
        push!(yield_values, val !== nothing ? val : Undef(ctx.ssavaluetypes[phi.ssa_idx]))
    end
    return YieldOp(yield_values)
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

#=============================================================================
 Loop Construction
=============================================================================#

"""
    build_while_op(tree::ControlTree, ir::IRCode, ctx::StructurizationContext)
        -> Tuple{WhileOp, Vector{Int}, Vector{Any}}

Build a WhileOp from a REGION_WHILE_LOOP control tree.
Returns (while_op, phi_indices, phi_types) where:
- while_op: The constructed WhileOp with before/after regions
- phi_indices: SSA indices of the header phi nodes (for getfield generation)
- phi_types: Julia types of the header phi nodes

The WhileOp structure:
- before: header statements + ConditionOp(condition, carried_args)
- after: body statements + YieldOp(carried_values)
"""
function build_while_op(tree::ControlTree, ir::IRCode, ctx::StructurizationContext)
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    header_idx = node_index(tree)
    loop_blocks = get_loop_blocks(tree, ir)
    nblocks = length(ir.cfg.blocks)

    @assert 1 <= header_idx <= nblocks "Invalid header_idx from control tree: $header_idx"
    header_bb = ir.cfg.blocks[header_idx]
    header_range = first(header_bb.stmts):last(header_bb.stmts)

    # Extract phi node information
    phi_info = extract_header_phis(header_idx, ir, loop_blocks)
    (; phi_indices, phi_types, init_values, carried_values) = phi_info

    # Find the condition for loop exit
    condition = nothing
    for si in header_range
        stmt = stmts[si]
        if stmt isa GotoIfNot
            condition = stmt.cond
            break
        end
    end

    # Build "before" region: header statements + ConditionOp
    before = Block()
    emit_condition_block_stmts!(before, header_idx, ir)

    condition_args = IRValue[SSAValue(idx) for idx in phi_indices]
    cond_value = condition !== nothing ? convert_phi_value(condition) : true
    before.terminator = ConditionOp(cond_value, condition_args)

    # Build "after" region: body statements + YieldOp
    after = Block()
    collect_loop_body_stmts!(after, tree, header_idx, ir, ctx)
    after.terminator = YieldOp(copy(carried_values))

    # Create BlockArgs and apply substitutions immediately
    subs = Substitutions()
    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
        arg = BlockArg(i, phi_type)
        push!(before.args, arg)
        push!(after.args, BlockArg(i, phi_type))
        subs[phi_idx] = arg
    end
    apply_substitutions!(before, subs)
    apply_substitutions!(after, subs)

    while_op = WhileOp(before, after, init_values)
    return while_op, phi_indices, phi_types
end

"""
    find_loop_exit_condition(ir::IRCode, loop_blocks::Set{Int})

Find the GotoIfNot in `loop_blocks` whose target exits the loop.
Returns `(; cond, idx, block)` or `nothing`.
"""
function find_loop_exit_condition(ir::IRCode, loop_blocks::Set{Int})
    for block_idx in loop_blocks
        bb = ir.cfg.blocks[block_idx]
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa GotoIfNot && stmt.dest ∉ loop_blocks
                return (; cond=stmt.cond, idx=si, block=block_idx, dest=stmt.dest)
            end
        end
    end
    return nothing
end

"""
    build_loop_op(tree::ControlTree, ir::IRCode, ctx::StructurizationContext)
        -> Tuple{LoopOp, Vector{Int}, Vector{Any}, Vector{Int}}

Build a LoopOp from a control tree and return phi node information.
Returns (loop_op, phi_indices, phi_types, post_loop_blocks) where:
- loop_op: The constructed LoopOp
- phi_indices: SSA indices of the header phi nodes (for getfield generation)
- phi_types: Julia types of the header phi nodes
- post_loop_blocks: block indices whose content should be emitted after the loop

Uses CFG-based natural loop blocks for exit detection, which correctly excludes
exit-target blocks that may have been absorbed into the control tree by
TERMINATION regions.
"""
function build_loop_op(tree::ControlTree, ir::IRCode, ctx::StructurizationContext)
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    header_idx = node_index(tree)
    nblocks = length(ir.cfg.blocks)

    @assert 1 <= header_idx <= nblocks "Invalid header_idx from control tree: $header_idx"

    # Use CFG-based natural loop blocks for exit detection.
    # The control tree may include exit-target blocks (via TERMINATION regions),
    # but the natural loop only contains blocks reachable from the header via backedges.
    natural_blocks = compute_natural_loop_blocks(ir, header_idx)

    # 1. Extract phis from header
    phi_info = extract_header_phis(header_idx, ir, natural_blocks)
    (; phi_indices, phi_types, init_values, carried_values) = phi_info

    # 2. Find exit condition (using natural loop blocks)
    exit = find_loop_exit_condition(ir, natural_blocks)

    # 3. Classify children: determine exit child, post-loop blocks, and cache
    #    child_blocks to avoid redundant get_region_blocks calls in step 4.
    exit_child_idx = nothing
    post_loop_set = Set{Int}()
    child_block_cache = Vector{Set{Int}}()
    for (i, child) in enumerate(children(tree))
        child_blocks = get_region_blocks(child, ir)
        push!(child_block_cache, child_blocks)
        if exit !== nothing
            if exit.block ∈ child_blocks
                exit_child_idx = i
            end
            for blk in child_blocks
                if blk ∉ natural_blocks && 1 <= blk <= nblocks
                    push!(post_loop_set, blk)
                end
            end
        end
    end

    # 4. Process children in two phases:
    #    - Up to and including the exit child → body (pre-condition stmts)
    #    - After the exit child → then_blk (post-condition stmts, continue branch)
    #    For children containing the exit block AND post-loop blocks (TERMINATION
    #    regions), only collect statements from the in-loop blocks directly.
    body = Block()
    then_blk = Block()

    for (i, child) in enumerate(children(tree))
        child_blocks = child_block_cache[i]

        # Skip children entirely outside the natural loop
        if !isempty(post_loop_set) && issubset(child_blocks, post_loop_set)
            continue
        end

        # For mixed children (e.g., TERMINATION with exit + post-loop blocks),
        # only collect statements from the in-loop blocks directly
        if !isempty(post_loop_set) && !isempty(intersect(child_blocks, post_loop_set))
            target = (exit_child_idx !== nothing && i > exit_child_idx) ? then_blk : body
            for blk_idx in sort!(collect(setdiff(child_blocks, post_loop_set)))
                collect_block_statements!(target, blk_idx, ir; capture_terminator=false)
            end
            continue
        end

        target = (exit_child_idx !== nothing && i > exit_child_idx) ? then_blk : body
        process_child_region!(target, child, ir, ctx)
    end

    # 5. Find and pad extra exit values into the loop-carry chain.
    extra_exits = if exit !== nothing
        find_extra_exit_values(ir, exit.dest, natural_blocks, Set(phi_indices))
    else
        @NamedTuple{value::IRValue, getfield_idx::Int, type::Any}[]
    end
    n_header_phis = length(phi_indices)
    pad_extra_exits!(extra_exits, init_values, carried_values, body, phi_indices, phi_types, n_header_phis)

    # 6. Build exit control flow
    if exit !== nothing
        cond_value = convert_phi_value(exit.cond)

        then_blk.terminator = ContinueOp(copy(carried_values))

        else_blk = Block()
        break_values = IRValue[v for v in carried_values]
        # Replace header phi carried values with SSAValue refs (they're block args)
        for (i, idx) in enumerate(phi_indices[1:n_header_phis])
            break_values[i] = SSAValue(idx)
        end
        else_blk.terminator = BreakOp(break_values)

        push!(body, exit.idx, IfOp(cond_value, then_blk, else_blk), Nothing)
    else
        body.terminator = ContinueOp(copy(carried_values))
    end

    # 7. BlockArgs for header phis + substitutions
    subs = Substitutions()
    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices[1:n_header_phis], phi_types))
        arg = BlockArg(i, phi_type)
        push!(body.args, arg)
        subs[phi_idx] = arg
    end
    apply_substitutions!(body, subs)

    loop_op = LoopOp(body, init_values)
    post_loop_blocks = sort!(collect(post_loop_set))

    return loop_op, phi_indices, phi_types, post_loop_blocks
end

"""
    build_for_op(tree::ControlTree, ir::IRCode, ctx::StructurizationContext)
        -> Tuple{ForOp, Vector{Int}, Vector{Any}}

Build a ForOp directly from a REGION_FOR_LOOP control tree using metadata from CFG analysis.
Returns (for_op, phi_indices, phi_types) where:
- for_op: The constructed ForOp with bounds, step, IV, and body
- phi_indices: SSA indices of the non-IV phi nodes (for getfield generation)
- phi_types: Julia types of the non-IV phi nodes

The ForOp structure:
- lower: Lower bound from ForLoopInfo
- upper: Upper bound (adjusted +1 if is_inclusive)
- step: Step value from ForLoopInfo
- iv_arg: BlockArg for the induction variable
- body: Loop body statements + ContinueOp with carried values
- init_values: Non-IV loop-carried values
"""
function build_for_op(block::Block, tree::ControlTree, ir::IRCode, ctx::StructurizationContext)
    stmts = ir.stmts.stmt
    types = ir.stmts.type
    header_idx = node_index(tree)
    loop_blocks = get_loop_blocks(tree, ir)
    for_info = metadata(tree)::ForLoopInfo
    nblocks = length(ir.cfg.blocks)

    @assert 1 <= header_idx <= nblocks "Invalid header_idx from control tree: $header_idx"
    header_bb = ir.cfg.blocks[header_idx]
    header_range = first(header_bb.stmts):last(header_bb.stmts)

    # Extract phi info with IV excluded from init/carried values
    iv_phi_idx = for_info.iv_phi_idx
    all_phi_info = extract_header_phis(header_idx, ir, loop_blocks; exclude_iv=iv_phi_idx)
    (; init_values, carried_values) = all_phi_info

    # Build result phi_indices and phi_types (excluding IV)
    phi_indices = Int[]
    phi_types = Any[]
    for (idx, typ) in zip(all_phi_info.phi_indices, all_phi_info.phi_types)
        if idx != iv_phi_idx
            push!(phi_indices, idx)
            push!(phi_types, typ)
        end
    end

    # Get IV type
    iv_type = types[iv_phi_idx]

    # Create BlockArg for IV (id=1, first in ForOp's block args)
    iv_arg = BlockArg(1, iv_type)

    # Build the body block
    body = Block()

    # Find the condition SSA from GotoIfNot and compute the condition chain to exclude
    cond_ssa = nothing
    for si in header_range
        stmt = stmts[si]
        if stmt isa GotoIfNot && stmt.cond isa SSAValue
            cond_ssa = stmt.cond
            break
        end
    end
    excluded = cond_ssa !== nothing ?
        find_condition_chain(stmts, header_range, cond_ssa) : Set{Int}()

    # Collect header statements (excluding phi nodes, control flow, and condition chain)
    for si in header_range
        stmt = stmts[si]
        if si ∉ excluded && !(stmt isa PhiNode || stmt isa GotoNode || stmt isa GotoIfNot || stmt isa ReturnNode)
            push!(body, si, stmt, types[si])
        end
    end

    # Process loop body blocks (excluding header)
    collect_loop_body_stmts!(body, tree, header_idx, ir, ctx)

    # Find and pad extra exit values into the loop-carry chain
    exit_info = find_loop_exit_condition(ir, loop_blocks)
    already_exported = Set{Int}([iv_phi_idx; phi_indices])
    extra_exits = if exit_info !== nothing
        find_extra_exit_values(ir, exit_info.dest, loop_blocks, already_exported)
    else
        @NamedTuple{value::IRValue, getfield_idx::Int, type::Any}[]
    end
    n_phi = length(phi_indices)
    pad_extra_exits!(extra_exits, init_values, carried_values, body, phi_indices, phi_types, n_phi + 1)

    # ContinueOp with non-IV carried values (including extra exits)
    body.terminator = ContinueOp(copy(carried_values))

    # Build ForOp with bounds from ForLoopInfo
    lower = convert_phi_value(for_info.lower)
    upper = convert_phi_value(for_info.upper)
    step = convert_phi_value(for_info.step)

    # If is_inclusive (Julia's 1:n), insert upper+1 in the parent block
    if for_info.is_inclusive
        adj_ssa_idx = ctx.next_ssa_idx
        ctx.next_ssa_idx += 1
        adj_upper = convert_phi_value(for_info.upper)
        upper_type = get_value_type(for_info.upper, ir)
        add_int_expr = Expr(:call, GlobalRef(Base, :add_int), adj_upper, one(upper_type))
        push!(block, adj_ssa_idx, add_int_expr, upper_type)
        upper = SSAValue(adj_ssa_idx)
    end

    # Create BlockArgs and apply substitutions immediately
    subs = Substitutions()
    subs[iv_phi_idx] = iv_arg  # IV at index 1

    # Non-IV loop-carried values at indices 2, 3, ...
    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices[1:n_phi], phi_types))
        arg = BlockArg(i + 1, phi_type)
        push!(body.args, arg)
        subs[phi_idx] = arg
    end

    apply_substitutions!(body, subs)

    for_op = ForOp(lower, for_info.is_inclusive ? for_info.upper : upper, step, iv_arg, body, init_values)

    return for_op, phi_indices, phi_types
end
