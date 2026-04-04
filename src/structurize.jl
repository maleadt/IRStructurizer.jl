# CFGToSCF-style structurization
#
# Replaces the pattern-matching structural analysis with a principled two-phase
# algorithm inspired by MLIR's CFGToSCF (Bahmann et al. 2015):
#   Phase 1: Lift cycles to LoopOps (via natural loop detection)
#   Phase 2: Lift branches to IfOps (via dominance-based region splitting)
# Both phases are applied recursively until no unstructured CF remains.
# A post-pass promotes LoopOps to WhileOp/ForOp where possible.

#=============================================================================
 Context
=============================================================================#

mutable struct StructurizeCtx
    ir::IRCode
    domtree::DomTree
    postdomtree::PostDomTree
    # header → set of block indices in the natural loop
    loop_map::Dict{Int, Set{Int}}
    next_ssa::Int
    next_arg::Int
    types::Vector{Any}
    ssa_remap::Dict{Int, Int}   # original → fresh (for inner defs)
end

function StructurizeCtx(ir::IRCode)
    domtree = construct_domtree(ir)
    postdomtree = construct_postdomtree(ir)
    loops = compute_natural_loops(ir, domtree)
    n = length(ir.stmts.stmt)
    StructurizeCtx(ir, domtree, postdomtree, loops, n + 1, 1, copy(ir.stmts.type), Dict{Int,Int}())
end

alloc_ssa!(ctx::StructurizeCtx) = (idx = ctx.next_ssa; ctx.next_ssa += 1; idx)
alloc_arg!(ctx::StructurizeCtx) = (id = ctx.next_arg; ctx.next_arg += 1; id)

"""Remap SSAValue references in a statement. Clones Expr to avoid mutating shared IRCode."""
function remap_stmt(@nospecialize(stmt), remap::Dict{Int, Int})
    isempty(remap) && return stmt
    if stmt isa Expr
        new_args = Any[remap_ssa_ref(a, remap) for a in stmt.args]
        return Expr(stmt.head, new_args...)
    elseif stmt isa PiNode
        return PiNode(remap_ssa_ref(stmt.val, remap), stmt.typ)
    else
        return stmt
    end
end

remap_ssa_ref(@nospecialize(val), remap::Dict{Int, Int}) =
    val isa SSAValue ? SSAValue(get(remap, val.id, val.id)) : val

#=============================================================================
 Natural Loop Detection
=============================================================================#

"""
    compute_natural_loops(ir, domtree) -> Dict{Int, Set{Int}}

Find all natural loops via backedge detection. A backedge src→header (where
header dominates src) defines a natural loop: header + all blocks that can
reach src without going through header.
"""
function compute_natural_loops(ir::IRCode, domtree::DomTree)
    loops = Dict{Int, Set{Int}}()
    for (i, bb) in enumerate(ir.cfg.blocks)
        for succ in bb.succs
            dominates(domtree, succ, i) || continue
            header = succ
            body = get!(Set{Int}, loops, header)
            push!(body, header)
            worklist = Int[i]
            while !isempty(worklist)
                b = pop!(worklist)
                b ∈ body && continue
                push!(body, b)
                for pred in ir.cfg.blocks[b].preds
                    pred ∉ body && push!(worklist, pred)
                end
            end
        end
    end
    loops
end

"""Return the innermost loop at `header` that is contained within `region_blocks`, or nothing."""
function get_loop_at(ctx::StructurizeCtx, header::Int, region_blocks::Set{Int})
    body = get(ctx.loop_map, header, nothing)
    body === nothing && return nothing
    # Only consider loops fully contained in the region
    issubset(body, region_blocks) || return nothing
    return body
end

#=============================================================================
 Irreducible CFG Normalization (entry multiplexer pre-pass)
=============================================================================#

"""
    normalize_irreducible(ir::IRCode) -> IRCode

If the CFG has irreducible cycles (multi-entry SCCs), insert entry multiplexer
blocks to make them reducible. Returns the original IRCode unchanged if already
reducible.

The multiplexer is a new block with a discriminator phi that dispatches to the
original entry blocks via GotoIfNot. All edges into the SCC are redirected to
the multiplexer, making the SCC a natural loop with a single entry.
"""
function normalize_irreducible(ir::IRCode)
    domtree = construct_domtree(ir)
    reach = CFGReachability(ir.cfg, domtree)

    # Find multi-entry SCCs
    scc_groups = Dict{Int, Set{Int}}()
    for (bb, scc_id) in enumerate(reach.scc)
        scc_id == 0 && continue
        bb_in_irreducible_loop(reach, bb) || continue
        push!(get!(Set{Int}, scc_groups, scc_id), bb)
    end

    irreducible_sccs = Tuple{Set{Int}, Vector{Int}}[]  # (blocks, entries)
    for (_, blocks) in scc_groups
        length(blocks) <= 1 && continue
        entries = sort!([bb for bb in blocks
                         if any(p -> p ∉ blocks, ir.cfg.blocks[bb].preds)])
        length(entries) >= 2 && push!(irreducible_sccs, (blocks, entries))
    end

    isempty(irreducible_sccs) && return ir

    # Copy IR for mutation
    ir = copy_ir(ir)

    for (scc_blocks, entries) in irreducible_sccs
        insert_entry_multiplexer!(ir, scc_blocks, entries)
    end

    return ir
end

"""Deep-copy an IRCode so we can mutate stmts, cfg blocks, and phis."""
function copy_ir(ir::IRCode)
    new_stmts = InstructionStream(
        copy(ir.stmts.stmt), copy(ir.stmts.type),
        copy(ir.stmts.info), copy(ir.stmts.line), copy(ir.stmts.flag))
    new_blocks = [BasicBlock(StmtRange(first(bb.stmts), last(bb.stmts)),
                             copy(bb.preds), copy(bb.succs))
                  for bb in ir.cfg.blocks]
    new_cfg = CFG(new_blocks, copy(ir.cfg.index))
    IRCode(new_stmts, new_cfg, ir.debuginfo, copy(ir.argtypes),
           copy(ir.meta), copy(ir.sptypes))
end

"""
Insert an entry multiplexer block for a multi-entry SCC.

For entries [E0, E1], creates block BBM that:
1. Has a discriminator phi (0 = E0, 1 = E1)
2. Has phis mirroring each entry's phis (union with Undef padding)
3. Dispatches to E0 (fallthrough) or E1 (branch) based on discriminator
4. All entry edges (external + back-edges) redirect to BBM
"""
function insert_entry_multiplexer!(ir::IRCode, scc_blocks::Set{Int}, entries::Vector{Int})
    nblocks = length(ir.cfg.blocks)
    n_stmts = length(ir.stmts.stmt)

    # Collect edges to redirect: all edges into entry blocks from outside or from SCC back-edges
    # An "entry edge" is any edge from a block NOT in the SCC to an SCC entry,
    # OR any back-edge from inside the SCC to an SCC entry.
    edges_to_redirect = Tuple{Int, Int, Int}[]  # (from, to, entry_index)
    for (ei, entry) in enumerate(entries)
        for pred in ir.cfg.blocks[entry].preds
            # Redirect ALL edges to entry blocks (external + internal back-edges)
            push!(edges_to_redirect, (pred, entry, ei))
        end
    end

    # Collect phis at each entry block
    entry_phis = [collect_entry_phis(ir, e) for e in entries]

    # --- Append multiplexer statements ---
    bbm_idx = nblocks + 1
    new_stmt_start = n_stmts + 1
    si = n_stmts

    # Discriminator phi: edges from all redirected sources
    si += 1
    disc_si = si
    disc_edges = Int32[]
    disc_values = Any[]
    for (from, _, ei) in edges_to_redirect
        push!(disc_edges, Int32(from))
        push!(disc_values, ei - 1)  # 0-indexed discriminator
    end
    push!(ir.stmts.stmt, PhiNode(disc_edges, disc_values))
    push!(ir.stmts.type, Int)
    push!(ir.stmts.info, NoCallInfo())
    push!(ir.stmts.line, Int32(0))
    push!(ir.stmts.flag, UInt32(0))

    # Union phis: for each entry's phi, create a multiplexer phi
    # that carries the value from the appropriate predecessor
    phi_ssa_map = Dict{Int, Int}()  # original_phi_si → multiplexer_phi_si
    for (ei, phis) in enumerate(entry_phis)
        for (orig_si, orig_type) in phis
            si += 1
            phi_edges = Int32[]
            phi_values = Vector{Any}(undef, 0)
            for (from, _, edge_ei) in edges_to_redirect
                push!(phi_edges, Int32(from))
                if edge_ei == ei
                    # This edge targets the same entry — use the original phi value
                    val = get_phi_value_for_edge(ir, orig_si, from)
                    push!(phi_values, val)
                else
                    # Different entry — Undef
                    push!(phi_values, Undef(orig_type))
                end
            end
            push!(ir.stmts.stmt, PhiNode(phi_edges, phi_values))
            push!(ir.stmts.type, orig_type)
            push!(ir.stmts.info, NoCallInfo())
            push!(ir.stmts.line, Int32(0))
            push!(ir.stmts.flag, UInt32(0))
            phi_ssa_map[orig_si] = si
        end
    end

    # Dispatch: compare discriminator and branch to correct entry.
    # Use GotoIfNot + GotoNode (not fallthrough) since BBM may not be
    # adjacent to E0 in block order.
    if length(entries) == 2
        si += 1
        cmp_si = si
        push!(ir.stmts.stmt, Expr(:call, GlobalRef(Base, :(===)), SSAValue(disc_si), 0))
        push!(ir.stmts.type, Bool)
        push!(ir.stmts.info, NoCallInfo())
        push!(ir.stmts.line, Int32(0))
        push!(ir.stmts.flag, UInt32(0))

        si += 1
        push!(ir.stmts.stmt, GotoIfNot(SSAValue(cmp_si), entries[2]))
        push!(ir.stmts.type, Any)
        push!(ir.stmts.info, NoCallInfo())
        push!(ir.stmts.line, Int32(0))
        push!(ir.stmts.flag, UInt32(0))

        # Explicit goto E0 (can't rely on fallthrough — BBM is appended at end)
        si += 1
        push!(ir.stmts.stmt, GotoNode(entries[1]))
        push!(ir.stmts.type, Any)
        push!(ir.stmts.info, NoCallInfo())
        push!(ir.stmts.line, Int32(0))
        push!(ir.stmts.flag, UInt32(0))
    else
        error("irreducible control flow with >2 entries not yet supported")
    end

    new_stmt_end = si

    # --- Create multiplexer basic block ---
    bbm = BasicBlock(StmtRange(new_stmt_start, new_stmt_end), Int[], Int[])
    push!(ir.cfg.blocks, bbm)
    # Extend cfg.index for new statements
    for _ in new_stmt_start:new_stmt_end
        push!(ir.cfg.index, bbm_idx)
    end

    # BBM successors: E0 (fallthrough) and E1 (branch target)
    push!(bbm.succs, entries[1])  # fallthrough
    length(entries) >= 2 && push!(bbm.succs, entries[2])

    # --- Redirect edges ---
    for (from, to, _) in edges_to_redirect
        # Remove old edge from→to
        filter!(!=(to), ir.cfg.blocks[from].succs)
        filter!(!=(from), ir.cfg.blocks[to].preds)

        # Add new edge from→BBM (if not already present)
        if bbm_idx ∉ ir.cfg.blocks[from].succs
            push!(ir.cfg.blocks[from].succs, bbm_idx)
        end
        if from ∉ bbm.preds
            push!(bbm.preds, from)
        end

        # Add BBM→to pred (if not already present)
        if bbm_idx ∉ ir.cfg.blocks[to].preds
            push!(ir.cfg.blocks[to].preds, bbm_idx)
        end

        # Update GotoNode/GotoIfNot at `from` to target BBM instead of `to`
        redirect_terminator!(ir, from, to, bbm_idx)
    end

    # --- Update phis at original entries ---
    # Replace single-edge phis with identity expressions so emit_block_stmts! emits them
    # (PhiNodes are skipped by the structurizer; these now have only the BBM edge)
    for (ei, entry) in enumerate(entries)
        phis = entry_phis[ei]
        for (orig_si, _) in phis
            mux_si = phi_ssa_map[orig_si]
            ir.stmts.stmt[orig_si] = SSAValue(mux_si)
        end
    end

    return ir
end

"""Collect phis at a block: returns [(ssa_idx, type), ...]"""
function collect_entry_phis(ir::IRCode, block::Int)
    result = Tuple{Int, Any}[]
    bb = ir.cfg.blocks[block]
    for si in first(bb.stmts):last(bb.stmts)
        ir.stmts.stmt[si] isa PhiNode && push!(result, (si, ir.stmts.type[si]))
    end
    result
end

"""Get the value a PhiNode carries from a specific predecessor edge."""
function get_phi_value_for_edge(ir::IRCode, phi_si::Int, from::Int)
    stmt = ir.stmts.stmt[phi_si]
    stmt isa PhiNode || return nothing
    for (idx, edge) in enumerate(stmt.edges)
        if Int(edge) == from && isassigned(stmt.values, idx)
            return stmt.values[idx]
        end
    end
    return nothing  # edge not found
end

"""Redirect a block's terminator from targeting `old_dest` to `new_dest`."""
function redirect_terminator!(ir::IRCode, from::Int, old_dest::Int, new_dest::Int)
    bb = ir.cfg.blocks[from]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        if stmt isa GotoNode && stmt.label == old_dest
            ir.stmts.stmt[si] = GotoNode(new_dest)
        elseif stmt isa GotoIfNot && stmt.dest == old_dest
            ir.stmts.stmt[si] = GotoIfNot(stmt.cond, new_dest)
        end
    end
end

#=============================================================================
 Entry Point
=============================================================================#

"""
    structurize(ir::IRCode) -> (Block, max_ssa, max_arg)

Convert flat IRCode into a structured Block with nested IfOp/LoopOp/WhileOp/ForOp.
"""
function structurize(ir::IRCode)
    ir = normalize_irreducible(ir)
    ctx = StructurizeCtx(ir)
    all_blocks = Set(1:length(ir.cfg.blocks))
    entry = structurize_region!(ctx, 1, all_blocks)
    promote_loops!(entry, ctx)
    return entry, ctx.next_ssa - 1, ctx.next_arg - 1
end

#=============================================================================
 Core Algorithm
=============================================================================#

"""
    MergePhiInfo

Info about a phi node at a merge/exit block. `edge_values` maps predecessor
block index → value on that edge.
"""
struct MergePhiInfo
    ssa_idx::Int
    edge_values::Dict{Int, Any}
end

"""
    LoopCtx

Optional context for structurizing loop bodies. When present, back-edges to
`header` become ContinueOp and edges outside `loop_blocks` become BreakOp.
"""
struct LoopCtx
    header::Int
    loop_blocks::Set{Int}
    carried_values::Vector{IRValue}
    break_values::Vector{IRValue}
end

"""
    structurize_region!(ctx, entry, region_blocks; merge_phis, loop_ctx) -> Block

Recursively structurize a set of basic blocks into a single Block.

- `merge_phis`: if provided, the block's terminator will be YieldOp with merge values.
- `loop_ctx`: if provided, back-edges/exits become ContinueOp/BreakOp.
"""
function structurize_region!(ctx::StructurizeCtx, entry::Int, region_blocks::Set{Int};
                              merge_phis::Union{Nothing, Vector{MergePhiInfo}}=nothing,
                              loop_ctx::Union{Nothing, LoopCtx}=nothing)
    block = Block()
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)
    current = entry
    last_block = entry

    while current !== nothing && current ∈ region_blocks
        last_block = current

        # --- Loop header? (only if not already inside this loop) ---
        if loop_ctx === nothing || current != loop_ctx.header
            loop_body = get_loop_at(ctx, current, region_blocks)
            if loop_body !== nothing
                exit_dest = emit_loop!(block, ctx, current, loop_body, region_blocks)
                # Update last_block to the loop's exit predecessor (for merge phi lookup)
                if exit_dest !== nothing
                    for b in loop_body
                        exit_dest ∈ ir.cfg.blocks[b].succs && (last_block = b)
                    end
                end
                current = resolve_dest(exit_dest, region_blocks, loop_ctx, block)
                continue
            end
        end

        # --- Emit non-phi/non-terminator statements ---
        emit_block_stmts!(block, ctx, current)

        # --- Handle terminator ---
        term = find_terminator(ir, current)

        if term isa ReturnNode
            if !isempty(ctx.ssa_remap) && isdefined(term, :val)
                val = remap_ssa_ref(term.val, ctx.ssa_remap)
                block.terminator = val === term.val ? term : ReturnNode(val)
            else
                block.terminator = term
            end
            return block
        elseif term isa GotoNode
            current = resolve_dest(term.label, region_blocks, loop_ctx, block)
        elseif term isa GotoIfNot
            next = emit_branch!(block, ctx, current, term, region_blocks, merge_phis, loop_ctx)
            if next === nothing
                return block
            end
            current = resolve_dest(next, region_blocks, loop_ctx, block)
        else
            # Fallthrough
            next = current + 1
            current = resolve_dest(next <= nblocks ? next : nothing,
                                    region_blocks, loop_ctx, block)
        end
    end

    # Region ended — set terminator if not already set
    if block.terminator === nothing && merge_phis !== nothing
        block.terminator = make_exit_yield(ir, merge_phis, last_block, block, ctx)
    end

    return block
end

"""
Resolve a destination block, checking loop boundaries.
Returns the dest to continue walking, or nothing if it's a loop exit/back-edge.
"""
function resolve_dest(dest, region_blocks::Set{Int},
                       loop_ctx::Union{Nothing, LoopCtx}, block::Block)
    dest === nothing && return nothing
    if loop_ctx !== nothing
        if dest == loop_ctx.header
            block.terminator === nothing &&
                (block.terminator = ContinueOp(copy(loop_ctx.carried_values)))
            return nothing
        elseif dest ∉ loop_ctx.loop_blocks
            block.terminator === nothing &&
                (block.terminator = BreakOp(copy(loop_ctx.break_values)))
            return nothing
        end
    end
    dest ∈ region_blocks ? dest : nothing
end

#=============================================================================
 Statement Emission
=============================================================================#

"""Emit non-phi, non-terminator statements from a basic block."""
function emit_block_stmts!(block::Block, ctx::StructurizeCtx, bb_idx::Int)
    ir = ctx.ir
    remap = ctx.ssa_remap
    bb = ir.cfg.blocks[bb_idx]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        (stmt isa PhiNode || stmt isa GotoNode ||
         stmt isa GotoIfNot || stmt isa ReturnNode) && continue
        idx = get(remap, si, si)
        stmt = remap_stmt(stmt, remap)
        push!(block, idx, stmt, ir.stmts.type[si])
    end
end

"""Find the terminator statement in a basic block."""
function find_terminator(ir::IRCode, bb_idx::Int)
    bb = ir.cfg.blocks[bb_idx]
    for si in first(bb.stmts):last(bb.stmts)
        s = ir.stmts.stmt[si]
        (s isa GotoIfNot || s isa GotoNode || s isa ReturnNode) && return s
    end
    return nothing  # fallthrough
end

#=============================================================================
 Branch Lifting (IfOp)
=============================================================================#

"""
    emit_branch!(block, ctx, current, gotoifnot, region_blocks, outer_merge_phis) -> next

Create an IfOp for a conditional branch. Returns the merge block index to
continue with, or nothing if both branches exit/diverge.
"""
function emit_branch!(block::Block, ctx::StructurizeCtx, current::Int,
                      gotoifnot::GotoIfNot, region_blocks::Set{Int},
                      outer_merge_phis::Union{Nothing, Vector{MergePhiInfo}},
                      loop_ctx::Union{Nothing, LoopCtx}=nothing)
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)

    # GotoIfNot: cond=false → dest, cond=true → fallthrough
    false_dest = gotoifnot.dest
    # Derive fallthrough from CFG successors (not current+1, which assumes sequential layout)
    bb_succs = ir.cfg.blocks[current].succs
    true_dest = length(bb_succs) == 1 ? only(bb_succs) :
                first(s for s in bb_succs if s != false_dest)
    cond = remap_ssa_ref(gotoifnot.cond, ctx.ssa_remap)

    # Determine branch regions and merge block using dominance
    then_blocks, else_blocks, merge = find_branch_regions(
        ctx, current, true_dest, false_dest, region_blocks)

    # If merge exists and is in region, extract its phis.
    # Skip phis at loop headers — UNLESS the header has multiple non-loop predecessors
    # (entry multiplexer case: branch must yield the correct entry values).
    is_multi_entry_header = if merge !== nothing && haskey(ctx.loop_map, merge)
        loop_body = ctx.loop_map[merge]
        count(p -> p ∉ loop_body, ir.cfg.blocks[merge].preds) > 1
    else
        false
    end
    merge_phis = if merge !== nothing && merge ∈ region_blocks &&
                   (!haskey(ctx.loop_map, merge) || is_multi_entry_header)
        phis = extract_merge_phis(ir, merge, region_blocks)
        # If merge has no phis, check its successors for phis
        # (handles pass-through merge blocks like in || patterns)
        if isempty(phis)
            for succ in ir.cfg.blocks[merge].succs
                if succ ∈ region_blocks && !haskey(ctx.loop_map, succ)
                    succ_phis = extract_merge_phis(ir, succ, region_blocks)
                    if !isempty(succ_phis)
                        # Absorb the pass-through block into the branch regions
                        # and use the successor as the real merge
                        merge = succ
                        phis = succ_phis
                        break
                    end
                end
            end
        end
        isempty(phis) ? nothing : phis
    else
        nothing
    end

    # Determine what to pass as exit phis to sub-regions
    # If both branches exit our region, they need to yield outer_merge_phis
    sub_merge_phis = if merge !== nothing && merge ∈ region_blocks
        merge_phis  # yield inner merge phis
    else
        outer_merge_phis  # propagate outer merge phis
    end

    # Build then/else blocks recursively (propagate loop_ctx for break/continue)
    then_blk = if !isempty(then_blocks)
        structurize_region!(ctx, true_dest, then_blocks;
                             merge_phis=sub_merge_phis, loop_ctx=loop_ctx)
    else
        make_empty_branch_block(true_dest, current, sub_merge_phis, loop_ctx, ir, ctx)
    end

    else_blk = if !isempty(else_blocks)
        structurize_region!(ctx, false_dest, else_blocks;
                             merge_phis=sub_merge_phis, loop_ctx=loop_ctx)
    else
        make_empty_branch_block(false_dest, current, sub_merge_phis, loop_ctx, ir, ctx)
    end

    if merge !== nothing && merge ∈ region_blocks && merge_phis !== nothing
        # --- Inner merge exists: standard IfOp ---
        set_branch_yields!(then_blk, merge_phis, then_blocks, current, ir, block, ctx)
        set_branch_yields!(else_blk, merge_phis, else_blocks, current, ir, block, ctx)

        if_op = IfOp(cond, then_blk, else_blk)
        phi_indices = [p.ssa_idx for p in merge_phis]
        phi_types = [ctx.types[p.ssa_idx] for p in merge_phis]
        emit_ifop_result!(block, if_op, phi_indices, phi_types, ctx)
        return merge
    elseif merge !== nothing && merge ∈ region_blocks
        # Merge exists but no phis
        set_yield_if_needed!(then_blk)
        set_yield_if_needed!(else_blk)
        if_op = IfOp(cond, then_blk, else_blk)
        push!(block, alloc_ssa!(ctx), if_op, Tuple{})
        # If merge is the loop header, both branches already handle the loop flow
        # (break/continue inside). Don't continue walking at the header.
        if loop_ctx !== nothing && merge == loop_ctx.header
            return nothing
        end
        return merge
    else
        # --- Both branches exit/diverge ---
        # sub_merge_phis was already passed to recursive calls, so YieldOps are set
        set_yield_if_needed!(then_blk)
        set_yield_if_needed!(else_blk)

        if_op = IfOp(cond, then_blk, else_blk)

        if outer_merge_phis !== nothing && !isempty(outer_merge_phis)
            # Use fresh indices for getfields — these are intermediate values
            # fed to YieldOp, not final definitions. The outermost emit_ifop_result!
            # (in the merge case) keeps the original phi indices.
            phi_types = [ctx.types[p.ssa_idx] for p in outer_merge_phis]
            if_ssa = alloc_ssa!(ctx)
            result_type = Tuple{phi_types...}
            push!(block, if_ssa, if_op, result_type)
            yield_values = IRValue[]
            for (i, phi_type) in enumerate(phi_types)
                fresh = alloc_ssa!(ctx)
                push!(block, fresh, Expr(:call, Core.getfield, SSAValue(if_ssa), i), phi_type)
                push!(yield_values, SSAValue(fresh))
            end
            block.terminator = YieldOp(yield_values)
        else
            push!(block, alloc_ssa!(ctx), if_op, Nothing)
        end
        return nothing
    end
end

"""Set yield terminator on a branch block for merge phis, if not already set."""
function set_branch_yields!(blk::Block, merge_phis::Vector{MergePhiInfo},
                            branch_blocks::Set{Int}, branch_entry::Int,
                            ir::IRCode, parent_block::Block, ctx::StructurizeCtx)
    blk.terminator !== nothing && return  # already set (e.g., ReturnNode, inner yield)

    # Find the exit block: the block in branch_blocks (or branch_entry if empty)
    # that has an edge to a merge phi predecessor
    exit_block = find_exit_predecessor(merge_phis, branch_blocks, branch_entry, ir)
    blk.terminator = make_yield_for_edge(ir, merge_phis, exit_block, blk, ctx)
end

"""Ensure a block has a terminator (YieldOp if nothing set)."""
function set_yield_if_needed!(blk::Block)
    blk.terminator === nothing && (blk.terminator = YieldOp())
end

"""Create an empty branch block with appropriate terminator for its destination."""
function make_empty_branch_block(dest::Int, from::Int,
                                  merge_phis::Union{Nothing, Vector{MergePhiInfo}},
                                  loop_ctx::Union{Nothing, LoopCtx},
                                  ir::IRCode, ctx::StructurizeCtx)
    b = Block()
    # Loop boundary?
    if loop_ctx !== nothing
        if dest == loop_ctx.header
            b.terminator = ContinueOp(copy(loop_ctx.carried_values))
            return b
        elseif dest ∉ loop_ctx.loop_blocks
            b.terminator = BreakOp(copy(loop_ctx.break_values))
            return b
        end
    end
    # Merge phis? Use reachability from dest to find the right phi edge value.
    if merge_phis !== nothing && !isempty(merge_phis)
        pred = find_exit_predecessor(merge_phis, Set{Int}([dest]), from, ir)
        b.terminator = make_yield_for_edge(ir, merge_phis, pred, b, ctx)
    end
    return b
end

"""
    find_exit_predecessor(merge_phis, blocks, fallback, ir)

Find the block whose edge to the merge carries the phi value for this branch.
Uses BFS from the branch region through successors (DREAM's reachability
principle: the value a branch contributes to a merge phi is determined by
which phi edge predecessor is reachable from that branch).
"""
function find_exit_predecessor(merge_phis::Vector{MergePhiInfo}, blocks::Set{Int},
                                fallback::Int, ir::IRCode)
    nblocks = length(ir.cfg.blocks)
    seeds = isempty(blocks) ? Set{Int}([fallback]) : blocks

    # Check seeds and fallback directly (before BFS)
    for b in seeds, phi in merge_phis
        haskey(phi.edge_values, b) && return b
    end
    for phi in merge_phis
        haskey(phi.edge_values, fallback) && return fallback
    end

    # BFS through successors of seeds (handles pass-through blocks)
    visited = copy(seeds)
    push!(visited, fallback)  # don't re-enter the branch source
    queue = Int[]
    for b in seeds
        1 <= b <= nblocks || continue
        for succ in ir.cfg.blocks[b].succs
            succ ∈ visited || push!(queue, succ)
        end
    end

    while !isempty(queue)
        b = popfirst!(queue)
        b ∈ visited && continue
        push!(visited, b)

        for phi in merge_phis
            haskey(phi.edge_values, b) && return b
        end

        1 <= b <= nblocks || continue
        for succ in ir.cfg.blocks[b].succs
            succ ∈ visited || push!(queue, succ)
        end
    end

    return fallback
end

"""Create a YieldOp with values from merge phis for a given predecessor edge."""
function make_yield_for_edge(ir::IRCode, merge_phis::Vector{MergePhiInfo},
                              pred::Int, blk::Block, ctx::StructurizeCtx)
    yield_values = IRValue[]
    remap = ctx.ssa_remap
    for phi in merge_phis
        val = get(phi.edge_values, pred, nothing)
        if val !== nothing
            val = remap_ssa_ref(val, remap)
            resolved = resolve_yield_value(blk, phi.ssa_idx, val, remap)
            push!(yield_values, resolved)
        else
            push!(yield_values, Undef(ctx.types[phi.ssa_idx]))
        end
    end
    return YieldOp(yield_values)
end

"""Create a YieldOp for exiting a region at `last_block`."""
function make_exit_yield(ir::IRCode, merge_phis::Vector{MergePhiInfo},
                          last_block::Int, blk::Block, ctx::StructurizeCtx)
    # Reuse find_exit_predecessor's BFS to find the right phi edge
    pred = find_exit_predecessor(merge_phis, Set{Int}([last_block]), last_block, ir)
    return make_yield_for_edge(ir, merge_phis, pred, blk, ctx)
end

"""
If the block already defines `phi_ssa_idx` (or its remapped index), yield that SSAValue.
Otherwise yield `default_val`.
"""
function resolve_yield_value(blk::Block, phi_ssa_idx::Int, default_val,
                              remap::Dict{Int, Int}=Dict{Int,Int}())
    idx = get(remap, phi_ssa_idx, phi_ssa_idx)
    haskey(blk.body, idx) ? SSAValue(idx) : default_val
end

#=============================================================================
 Branch Region Splitting (dominance-based)
=============================================================================#

"""
    find_branch_regions(ctx, current, true_dest, false_dest, region_blocks)
        -> (then_blocks, else_blocks, merge)

Split region_blocks into then/else regions using dominance.
A successor with a single predecessor gets all blocks it dominates.
A successor with multiple predecessors is a merge block (empty region).
"""
function find_branch_regions(ctx::StructurizeCtx, current::Int,
                              true_dest::Int, false_dest::Int,
                              region_blocks::Set{Int})
    ir = ctx.ir
    nblocks = length(ir.cfg.blocks)

    then_blocks = Set{Int}()
    else_blocks = Set{Int}()

    # Collect blocks dominated by each successor (if single-entry from outside).
    # A successor is "single-entry" if only one predecessor from the region is
    # NOT a loop backedge to it. Loop backedges don't count because the loop body
    # is structurally inside the branch, not a separate entry path.
    if true_dest ∈ region_blocks && true_dest <= nblocks &&
       count_non_backedge_preds(ir, ctx, true_dest, region_blocks) == 1
        collect_dominated!(then_blocks, ctx.domtree, true_dest, region_blocks)
    end

    if false_dest ∈ region_blocks && false_dest <= nblocks &&
       count_non_backedge_preds(ir, ctx, false_dest, region_blocks) == 1
        collect_dominated!(else_blocks, ctx.domtree, false_dest, region_blocks)
    end

    # Remove any overlap with loop bodies that will be handled separately
    # (a block should only be in one region)
    setdiff!(then_blocks, else_blocks)

    # Merge = the block where all paths from `current` reconverge.
    # Prefer the immediate post-dominator (structurally exact).
    # Fall back to successor-candidate search when early returns prevent
    # real post-dominance (ipdom = 0 = virtual exit).
    merge = nothing
    ipdom = ctx.postdomtree.idoms_bb[current]
    if ipdom != 0 && ipdom ∈ region_blocks && ipdom ∉ then_blocks && ipdom ∉ else_blocks
        merge = ipdom
    else
        candidates = Set{Int}()
        for b in then_blocks
            for s in ir.cfg.blocks[b].succs
                s ∉ then_blocks && s != current && push!(candidates, s)
            end
        end
        for b in else_blocks
            for s in ir.cfg.blocks[b].succs
                s ∉ else_blocks && s != current && push!(candidates, s)
            end
        end
        if true_dest ∈ region_blocks && true_dest ∉ then_blocks
            push!(candidates, true_dest)
        end
        if false_dest ∈ region_blocks && false_dest ∉ else_blocks
            push!(candidates, false_dest)
        end
        for c in sort!(collect(candidates))
            if c ∈ region_blocks && c ∉ then_blocks && c ∉ else_blocks
                merge = c
                break
            end
        end
    end

    return then_blocks, else_blocks, merge
end

"""Count predecessors of `block` in `region` that are not loop backedges to `block`."""
function count_non_backedge_preds(ir::IRCode, ctx::StructurizeCtx, block::Int, region::Set{Int})
    count = 0
    for pred in ir.cfg.blocks[block].preds
        pred ∈ region || continue
        # A backedge is an edge where the target dominates the source
        if dominates(ctx.domtree, block, pred)
            continue  # skip loop backedge
        end
        count += 1
    end
    count
end


"""Collect all blocks in `region` dominated by `root` (including root itself)."""
function collect_dominated!(result::Set{Int}, domtree::DomTree, root::Int, region::Set{Int})
    root ∈ region || return
    push!(result, root)
    for child in domtree.nodes[root].children
        child ∈ region && collect_dominated!(result, domtree, child, region)
    end
end

#=============================================================================
 Merge Phi Extraction
=============================================================================#

"""Extract phi nodes at `merge_idx` that have edges from blocks in `region`."""
function extract_merge_phis(ir::IRCode, merge_idx::Int, region_blocks::Set{Int})
    result = MergePhiInfo[]
    nblocks = length(ir.cfg.blocks)
    1 <= merge_idx <= nblocks || return result

    bb = ir.cfg.blocks[merge_idx]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa PhiNode || continue

        edge_values = Dict{Int, Any}()
        for (edge_idx, edge) in enumerate(stmt.edges)
            if isassigned(stmt.values, edge_idx)
                # Include edges from region blocks AND direct predecessors
                edge_values[Int(edge)] = stmt.values[edge_idx]
            end
        end
        !isempty(edge_values) && push!(result, MergePhiInfo(si, edge_values))
    end
    return result
end

#=============================================================================
 IfOp Result Emission
=============================================================================#

"""Push an IfOp and generate getfield statements at each phi index."""
function emit_ifop_result!(block::Block, if_op::IfOp, phi_indices::Vector{Int},
                            phi_types::AbstractVector, ctx::StructurizeCtx)
    if_ssa = alloc_ssa!(ctx)
    remap = ctx.ssa_remap
    if !isempty(phi_indices)
        result_type = Tuple{phi_types...}
        push!(block, if_ssa, if_op, result_type)
        for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
            idx = get(remap, phi_idx, phi_idx)
            push!(block, idx, Expr(:call, Core.getfield, SSAValue(if_ssa), i), phi_type)
        end
    else
        push!(block, if_ssa, if_op, Tuple{})
    end
    return if_ssa
end

#=============================================================================
 Loop Lifting (LoopOp)
=============================================================================#

"""
    emit_loop!(block, ctx, header, loop_blocks, region_blocks) -> exit_dest

Build a LoopOp for the natural loop at `header` and emit it into `block`.
Returns the exit destination block (may be outside region_blocks).
"""
function emit_loop!(block::Block, ctx::StructurizeCtx, header::Int,
                     loop_blocks::Set{Int}, region_blocks::Set{Int})
    ir = ctx.ir

    # 1. Extract header phi nodes
    phi_info = extract_loop_phis(ir, header, loop_blocks)

    # 2. Find exit destination
    exit_dest = find_loop_exit(ir, loop_blocks)

    # 3. Find extra exit values (loop-internal SSAs used outside)
    already_exported = Set{Int}(p.ssa_idx for p in phi_info)
    extra_exits = find_extra_exit_values(ir, loop_blocks, already_exported)

    # 4. Build init/carried values and block arguments
    init_values = IRValue[]
    carried_values = IRValue[]
    phi_indices = Int[]
    phi_types = Any[]
    body = Block()
    subs = Dict{Int, BlockArgument}()

    for phi in phi_info
        # If a preceding IfOp already defined this phi SSA (via getfield),
        # use that as init_val — it captures the correct branch-selected value.
        init_val = haskey(block.body, phi.ssa_idx) ? SSAValue(phi.ssa_idx) : phi.entry_val
        push!(init_values, init_val)
        push!(carried_values, phi.carried_val)
        push!(phi_indices, phi.ssa_idx)
        push!(phi_types, ctx.types[phi.ssa_idx])
        arg = BlockArgument(alloc_arg!(ctx), ctx.types[phi.ssa_idx])
        push!(body.args, arg)
        subs[phi.ssa_idx] = arg
    end

    # Save remap state and add extra-exit remappings for the loop body.
    # Inner defs get fresh indices; outer getfields keep the originals.
    saved_remap = copy(ctx.ssa_remap)
    for ex in extra_exits
        fresh = alloc_ssa!(ctx)
        ctx.ssa_remap[ex.ssa_idx] = fresh
        push!(init_values, Undef(ex.type))
        push!(carried_values, SSAValue(fresh))  # carry the fresh-index value
        push!(phi_indices, ex.ssa_idx)           # getfield OUTSIDE uses original
        push!(phi_types, ex.type)
        arg = BlockArgument(alloc_arg!(ctx), ex.type)
        push!(body.args, arg)
    end

    # Remap header phi carried values that reference extra exit SSAs
    if !isempty(ctx.ssa_remap)
        n_header = length(phi_info)
        for i in 1:n_header
            v = carried_values[i]
            if v isa SSAValue
                carried_values[i] = SSAValue(get(ctx.ssa_remap, v.id, v.id))
            end
        end
    end

    # 5. Build loop body
    build_loop_body!(body, ctx, header, loop_blocks, carried_values, subs)

    # Restore remap (scoped to loop body)
    ctx.ssa_remap = saved_remap

    # 6. Apply phi→arg substitutions
    apply_substitutions!(body, subs, ctx)

    # 7. Emit LoopOp + getfields
    loop_op = LoopOp(body, init_values)
    loop_ssa = alloc_ssa!(ctx)
    result_type = Tuple{phi_types...}
    push!(block, loop_ssa, loop_op, result_type)

    for (i, (phi_idx, phi_type)) in enumerate(zip(phi_indices, phi_types))
        push!(block, phi_idx, Expr(:call, Core.getfield, SSAValue(loop_ssa), i), phi_type)
    end

    return exit_dest
end

#=============================================================================
 Loop Body Construction
=============================================================================#

"""
Build the body of a LoopOp using `structurize_region!` with a LoopCtx.
The LoopCtx makes the region walk loop-aware: back-edges → ContinueOp, exits → BreakOp.
"""
function build_loop_body!(body::Block, ctx::StructurizeCtx, header::Int,
                           loop_blocks::Set{Int}, carried_values::Vector{IRValue},
                           subs::Dict{Int, BlockArgument})
    break_values = IRValue[arg for arg in body.args]
    # Extra exits (beyond header phis) must carry the current iteration's
    # computed value, not the stale block arg from the previous iteration.
    n_header_phis = length(subs)
    for i in (n_header_phis + 1):length(break_values)
        break_values[i] = carried_values[i]
    end
    lctx = LoopCtx(header, loop_blocks, carried_values, break_values)

    # Use structurize_region! with loop context for the entire loop body
    content = structurize_region!(ctx, header, loop_blocks; loop_ctx=lctx)

    # Merge content into the pre-existing body (which already has args)
    merge_block_into!(body, content)
end

"""Merge the content of `src` into `dst` (body + terminator)."""
function merge_block_into!(dst::Block, src::Block)
    for (idx, entry) in src.body
        push!(dst.body, (idx, entry.stmt, entry.typ))
    end
    if src.terminator !== nothing && dst.terminator === nothing
        dst.terminator = src.terminator
    end
end

#=============================================================================
 Loop Analysis Helpers
=============================================================================#

struct LoopPhiInfo
    ssa_idx::Int
    entry_val::Any
    carried_val::Any
end

"""Extract phi nodes from a loop header, separating entry and carried values."""
function extract_loop_phis(ir::IRCode, header::Int, loop_blocks::Set{Int})
    result = LoopPhiInfo[]
    bb = ir.cfg.blocks[header]
    for si in first(bb.stmts):last(bb.stmts)
        stmt = ir.stmts.stmt[si]
        stmt isa PhiNode || continue
        entry_val = nothing
        carried_val = nothing
        for (edge_idx, edge) in enumerate(stmt.edges)
            isassigned(stmt.values, edge_idx) || continue
            val = stmt.values[edge_idx]
            if Int(edge) ∈ loop_blocks
                carried_val = val
            else
                entry_val = val
            end
        end
        if entry_val !== nothing && carried_val !== nothing
            push!(result, LoopPhiInfo(si, entry_val, carried_val))
        elseif entry_val !== nothing || carried_val !== nothing
            # A phi with edges from only one side of the loop boundary is
            # malformed — the optimizer may have removed a dead edge, or
            # the loop has unusual structure. Error rather than silently
            # producing wrong loop-carried values.
            has_entry = entry_val !== nothing
            error("internal error: loop header phi %$si at BB$header has ",
                  has_entry ? "entry" : "carried", " value but no ",
                  has_entry ? "carried" : "entry", " value")
        end
    end
    result
end

"""Find the block index that the loop exits to (first successor outside loop_blocks)."""
function find_loop_exit(ir::IRCode, loop_blocks::Set{Int})
    for b in loop_blocks
        for succ in ir.cfg.blocks[b].succs
            succ ∉ loop_blocks && return succ
        end
    end
    return nothing
end

"""Find all blocks outside `loop_blocks` that are successors of loop blocks."""
function find_loop_exits(ir::IRCode, loop_blocks::Set{Int})
    exits = Set{Int}()
    for b in loop_blocks
        for succ in ir.cfg.blocks[b].succs
            succ ∉ loop_blocks && push!(exits, succ)
        end
    end
    exits
end

"""
Find loop-internal SSA values referenced outside the loop.

Scans blocks reachable from loop exit edges (not the entire IR). This is more
precise than scanning all non-loop blocks: it excludes blocks before the loop
or on branches that bypass it. Values escape through exit-block phis, direct
references at downstream blocks, or as operands of sequential loops.
"""
function find_extra_exit_values(ir::IRCode, loop_blocks::Set{Int},
                                 already_exported::Set{Int})
    result = @NamedTuple{ssa_idx::Int, value::Any, type::Any}[]
    seen = Set{Int}()

    # Collect all non-loop blocks reachable from loop exit edges
    reachable = Set{Int}()
    worklist = Int[]
    for b in loop_blocks
        for succ in ir.cfg.blocks[b].succs
            succ ∉ loop_blocks && push!(worklist, succ)
        end
    end
    while !isempty(worklist)
        b = pop!(worklist)
        b ∈ reachable && continue
        b ∈ loop_blocks && continue
        push!(reachable, b)
        for succ in ir.cfg.blocks[b].succs
            succ ∉ reachable && succ ∉ loop_blocks && push!(worklist, succ)
        end
    end

    for blk_idx in reachable
        bb = ir.cfg.blocks[blk_idx]
        for si in first(bb.stmts):last(bb.stmts)
            stmt = ir.stmts.stmt[si]
            if stmt isa PhiNode
                si ∈ already_exported && continue
                for (edge_idx, edge) in enumerate(stmt.edges)
                    if isassigned(stmt.values, edge_idx) && Int(edge) ∈ loop_blocks
                        loop_val = stmt.values[edge_idx]
                        gf_idx = loop_val isa SSAValue ? loop_val.id : si
                        gf_idx ∈ seen && continue
                        gf_idx ∈ already_exported && continue
                        push!(result, (; ssa_idx=gf_idx, value=loop_val, type=ir.stmts.type[si]))
                        push!(seen, gf_idx)
                    end
                end
            else
                # Single-predecessor exit blocks may reference loop values directly
                for arg in stmt_ssa_uses(stmt)
                    is_defined_in(arg, loop_blocks, ir) || continue
                    arg.id ∈ already_exported && continue
                    arg.id ∈ seen && continue
                    push!(result, (; ssa_idx=arg.id, value=arg, type=ir.stmts.type[arg.id]))
                    push!(seen, arg.id)
                end
            end
        end
    end
    result
end

function stmt_ssa_uses(stmt)
    if stmt isa Expr
        return Iterators.filter(x -> x isa SSAValue, stmt.args)
    elseif stmt isa GotoIfNot && stmt.cond isa SSAValue
        return (stmt.cond,)
    elseif stmt isa ReturnNode && isdefined(stmt, :val) && stmt.val isa SSAValue
        return (stmt.val,)
    else
        return ()
    end
end

function is_defined_in(val::SSAValue, blocks::Set{Int}, ir::IRCode)
    for blk_idx in blocks
        bb = ir.cfg.blocks[blk_idx]
        val.id in first(bb.stmts):last(bb.stmts) && return true
    end
    false
end
is_defined_in(val, blocks, ir) = false
