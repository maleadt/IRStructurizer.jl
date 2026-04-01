# Loop construction: build_while_op, build_loop_op, build_for_op

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

    # Create BlockArguments and apply substitutions immediately
    subs = Substitutions()
    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
        arg = BlockArgument(i, phi_type)
        push!(before.args, arg)
        push!(after.args, BlockArgument(i, phi_type))
        subs[phi_idx] = arg
    end
    apply_substitutions!(before, subs)
    apply_substitutions!(after, subs)

    while_op = WhileOp(before, after, init_values)
    return while_op, phi_indices, phi_types
end

"""
    find_loop_exit_condition(ir::IRCode, loop_blocks::Set{Int})

Find the GotoIfNot in `loop_blocks` that controls the loop exit.
Returns `(; cond, idx, block, dest, inverted)` or `nothing`.

A `GotoIfNot(cond, dest)` has two successors:
- `dest` (taken when `cond` is false)
- fallthrough to the next block (taken when `cond` is true)

When `dest` exits the loop: `inverted=false` (cond=true → stay, cond=false → exit).
When the fallthrough exits: `inverted=true` (cond=true → exit, cond=false → stay).
"""
function find_loop_exit_condition(ir::IRCode, loop_blocks::Set{Int})
    nblocks = length(ir.cfg.blocks)
    for block_idx in loop_blocks
        bb = ir.cfg.blocks[block_idx]
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa GotoIfNot
                if stmt.dest ∉ loop_blocks
                    return (; cond=stmt.cond, idx=si, block=block_idx, dest=stmt.dest, inverted=false)
                end
                # Check fallthrough successor (next block in sequence)
                fallthrough = block_idx + 1
                if fallthrough <= nblocks && fallthrough ∉ loop_blocks
                    return (; cond=stmt.cond, idx=si, block=block_idx, dest=fallthrough, inverted=true)
                end
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

    # 5. BlockArguments for header phis + substitutions
    # NOTE: must happen before pad_extra_exits! so body.args order matches
    # init_values/carried_values order (header phis first, then extra exits).
    n_header_phis = length(phi_indices)
    subs = Substitutions()
    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices[1:n_header_phis], phi_types))
        arg = BlockArgument(i, phi_type)
        push!(body.args, arg)
        subs[phi_idx] = arg
    end

    # 6. Find and pad extra exit values into the loop-carry chain.
    extra_exits = if exit !== nothing
        find_extra_exit_values(ir, exit.dest, natural_blocks, Set(phi_indices))
    else
        @NamedTuple{value::IRValue, getfield_idx::Int, type::Any}[]
    end
    pad_extra_exits!(extra_exits, init_values, carried_values, body, phi_indices, phi_types, n_header_phis)

    # 7. Build exit control flow
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

        if exit.inverted
            # Exit through fallthrough: cond=true → exit, cond=false → stay in loop
            push!(body, exit.idx, IfOp(cond_value, else_blk, then_blk), Nothing)
        else
            # Exit through goto dest: cond=true → stay in loop, cond=false → exit
            push!(body, exit.idx, IfOp(cond_value, then_blk, else_blk), Nothing)
        end
    else
        body.terminator = ContinueOp(copy(carried_values))
    end

    apply_substitutions!(body, subs)

    loop_op = LoopOp(body, init_values)

    # Collect post-loop children: children entirely outside the natural loop,
    # or the post-loop subtrees of mixed children (e.g., TERMINATION regions
    # that span loop exit + post-loop code).
    post_loop_children = ControlTree[]
    for (i, child) in enumerate(children(tree))
        child_blocks = child_block_cache[i]
        if !isempty(post_loop_set) && issubset(child_blocks, post_loop_set)
            # Entirely post-loop child — needs full structurization
            push!(post_loop_children, child)
        elseif !isempty(post_loop_set) && !isempty(intersect(child_blocks, post_loop_set))
            # Mixed child — extract the post-loop subtrees
            for sub in children(child)
                sub_blocks = get_region_blocks(sub, ir)
                if issubset(sub_blocks, post_loop_set)
                    push!(post_loop_children, sub)
                end
            end
        end
    end

    return loop_op, phi_indices, phi_types, post_loop_children
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
- upper: Exclusive upper bound (adjusted +1 for inclusive patterns like `<=`)
- step: Step value from ForLoopInfo
- iv_arg: BlockArgument for the induction variable
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

    # Create BlockArgument for IV (id=1, first in ForOp's block args)
    iv_arg = BlockArgument(1, iv_type)

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

    # Create BlockArguments for header phis BEFORE padding extra exits,
    # so body.args order matches init_values/carried_values order
    # (header phis first, then extra exits).
    subs = Substitutions()
    subs[iv_phi_idx] = iv_arg  # IV at index 1
    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices[1:n_phi], phi_types))
        arg = BlockArgument(i + 1, phi_type)
        push!(body.args, arg)
        subs[phi_idx] = arg
    end

    pad_extra_exits!(extra_exits, init_values, carried_values, body, phi_indices, phi_types, n_phi + 1)

    # ContinueOp with non-IV carried values (including extra exits)
    body.terminator = ContinueOp(copy(carried_values))

    # Build ForOp with bounds from ForLoopInfo.
    # ForOp uses exclusive upper bound semantics (loop iterates while iv < upper).
    lower = convert_phi_value(for_info.lower)
    upper = convert_phi_value(for_info.upper)
    step = convert_phi_value(for_info.step)

    # Normalize inclusive bounds (e.g., `while j <= n`) to exclusive (upper + 1)
    if for_info.is_inclusive
        adj_ssa_idx = ctx.next_ssa_idx
        ctx.next_ssa_idx += 1
        upper_type = get_value_type(for_info.upper, ir)
        add_int_expr = Expr(:call, GlobalRef(Base, :add_int), upper, one(upper_type))
        push!(block, adj_ssa_idx, add_int_expr, upper_type)
        upper = SSAValue(adj_ssa_idx)
    end

    apply_substitutions!(body, subs)

    for_op = ForOp(lower, upper, step, iv_arg, body, init_values)

    return for_op, phi_indices, phi_types
end
