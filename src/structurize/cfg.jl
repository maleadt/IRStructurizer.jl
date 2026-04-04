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

    # --- Create exit latch ---
    # Consolidates all back-edges and exit edges into a single latch block.
    # Back-edges (shouldRepeat=1) → loop header. Exit edges (shouldRepeat=0) → exit block.
    insert_exit_latch!(ir, scc_blocks, entries, bbm_idx, disc_si, phi_ssa_map)

    return ir
end

"""
Insert an exit latch block that consolidates back-edges and exit edges.

All edges leaving SCC blocks (back-edges to multiplexer + exits to return blocks)
are redirected to the latch. The latch has a shouldRepeat flag that dispatches:
  shouldRepeat=1 → loop header (multiplexer) with carried values
  shouldRepeat=0 → exit block with return value

This gives the loop exactly one back-edge and one exit edge.
"""
function insert_exit_latch!(ir::IRCode, scc_blocks::Set{Int}, entries::Vector{Int},
                              bbm_idx::Int, disc_si::Int, phi_ssa_map::Dict{Int, Int})
    nblocks = length(ir.cfg.blocks)
    si = length(ir.stmts.stmt)

    # Classify edges from SCC blocks
    # back_edges: SCC block → entry block (now BBM after mux redirect)
    # exit_edges: SCC block → return block (outside SCC)
    back_edges = Tuple{Int, Int}[]   # (from, original_entry_idx)
    exit_edges = Tuple{Int, Int, Any}[]  # (from, exit_block, return_value)

    for b in scc_blocks
        for succ in ir.cfg.blocks[b].succs
            if succ == bbm_idx
                # Back-edge: determine which entry it targets from disc phi
                # Find the disc value this block carries
                disc_stmt = ir.stmts.stmt[disc_si]
                disc_val = 0
                for (idx, edge) in enumerate(disc_stmt.edges)
                    Int(edge) == b && (disc_val = disc_stmt.values[idx])
                end
                push!(back_edges, (b, disc_val))
            elseif succ ∉ scc_blocks && succ != bbm_idx
                # Exit edge: extract the return value from the exit block
                exit_bb = ir.cfg.blocks[succ]
                ret_val = nothing
                for esi in first(exit_bb.stmts):last(exit_bb.stmts)
                    s = ir.stmts.stmt[esi]
                    if s isa ReturnNode && isdefined(s, :val)
                        ret_val = s.val
                    end
                end
                push!(exit_edges, (b, succ, ret_val))
            end
        end
    end

    (isempty(back_edges) && isempty(exit_edges)) && return

    # --- Create latch block (BBL) ---
    bbl_idx = nblocks + 1
    latch_start = si + 1

    # Exit-edge predecessors to the latch are the EXIT BLOCKS (BB4, BB7),
    # not the SCC blocks that branch to them (BB3, BB6).
    exit_block_set = Set{Int}(eb for (_, eb, _) in exit_edges)

    # Phi 1: shouldRepeat (1 for back-edges, 0 for exit edges)
    si += 1; sr_si = si
    sr_edges = Int32[]; sr_values = Any[]
    for (from, _) in back_edges
        push!(sr_edges, Int32(from)); push!(sr_values, true)
    end
    for eb in exit_block_set
        push!(sr_edges, Int32(eb)); push!(sr_values, false)
    end
    append_stmt!(ir, si, PhiNode(sr_edges, sr_values), Bool)

    # Phi 2: disc value (for back-edge → header, dummy for exit)
    si += 1; latch_disc_si = si
    ld_edges = Int32[]; ld_values = Any[]
    for (from, disc_val) in back_edges
        push!(ld_edges, Int32(from)); push!(ld_values, disc_val)
    end
    for eb in exit_block_set
        push!(ld_edges, Int32(eb)); push!(ld_values, 0)
    end
    append_stmt!(ir, si, PhiNode(ld_edges, ld_values), Int)

    # Phis for each multiplexer union phi value (carried back to header)
    latch_carry_sis = Int[]
    for (orig_si, mux_si) in sort(collect(phi_ssa_map), by=first)
        si += 1
        push!(latch_carry_sis, si)
        phi_edges = Int32[]; phi_values = Any[]
        # Back-edges: carry the value from the multiplexer phi for this entry
        mux_phi = ir.stmts.stmt[mux_si]
        for (from, _) in back_edges
            # Find the value this block would carry for this phi
            val = nothing
            if mux_phi isa PhiNode
                for (idx, edge) in enumerate(mux_phi.edges)
                    Int(edge) == from && (val = mux_phi.values[idx])
                end
            end
            push!(phi_edges, Int32(from))
            push!(phi_values, something(val, Undef(ir.stmts.type[mux_si])))
        end
        # Exit blocks: Undef (not going back to header)
        for eb in exit_block_set
            push!(phi_edges, Int32(eb))
            push!(phi_values, Undef(ir.stmts.type[mux_si]))
        end
        append_stmt!(ir, si, PhiNode(phi_edges, phi_values), ir.stmts.type[mux_si])
    end

    # Phi for return value (from exit blocks, Undef from back-edges)
    si += 1; ret_val_si = si
    rv_edges = Int32[]; rv_values = Any[]
    # Determine return type from exit blocks
    ret_type = Any
    for (_, eb, rv) in exit_edges
        if rv !== nothing
            ret_type = ir.stmts.type[rv isa SSAValue ? rv.id : first(ir.cfg.blocks[eb].stmts)]
            break
        end
    end
    for (from, _) in back_edges
        push!(rv_edges, Int32(from)); push!(rv_values, Undef(ret_type))
    end
    # Group exit values by exit block
    for (_, eb, ret_val) in exit_edges
        if Int32(eb) ∉ rv_edges
            push!(rv_edges, Int32(eb))
            push!(rv_values, something(ret_val, Undef(ret_type)))
        end
    end
    append_stmt!(ir, si, PhiNode(rv_edges, rv_values), ret_type)

    # Dispatch: GotoIfNot(shouldRepeat, exit_block) + GotoNode(header)
    bbx_idx = bbl_idx + 1  # exit block index

    si += 1
    append_stmt!(ir, si, GotoIfNot(SSAValue(sr_si), bbx_idx), Any)
    si += 1
    append_stmt!(ir, si, GotoNode(bbm_idx), Any)

    latch_end = si

    # --- Create exit block (BBX) ---
    bbx_start = si + 1
    si += 1
    append_stmt!(ir, si, ReturnNode(SSAValue(ret_val_si)), Any)
    bbx_end = si

    # --- Add blocks to CFG ---
    bbl = BasicBlock(StmtRange(latch_start, latch_end), Int[], Int[])
    push!(ir.cfg.blocks, bbl)
    for s in latch_start:latch_end; push!(ir.cfg.index, bbl_idx); end

    bbx = BasicBlock(StmtRange(bbx_start, bbx_end), Int[bbl_idx], Int[])
    push!(ir.cfg.blocks, bbx)
    for s in bbx_start:bbx_end; push!(ir.cfg.index, bbx_idx); end

    # Latch succs: exit block + header
    push!(bbl.succs, bbx_idx)
    push!(bbl.succs, bbm_idx)
    # Header now has latch as predecessor (will update phis below)
    push!(ir.cfg.blocks[bbm_idx].preds, bbl_idx)
    push!(ir.cfg.blocks[bbm_idx].succs, bbl_idx)  # not really a succ, but for edge tracking

    # --- Redirect back-edges: SCC→BBM to SCC→BBL ---
    for (from, _) in back_edges
        filter!(!=(bbm_idx), ir.cfg.blocks[from].succs)
        push!(ir.cfg.blocks[from].succs, bbl_idx)
        filter!(!=(from), ir.cfg.blocks[bbm_idx].preds)
        push!(bbl.preds, from)
        redirect_terminator!(ir, from, bbm_idx, bbl_idx)
    end

    # --- Redirect exit edges: convert exit blocks (return) to pass-through (goto latch) ---
    # Don't redirect the predecessor's terminator (would destroy GotoIfNot).
    # Instead, replace the exit block's ReturnNode with GotoNode(latch).
    redirected_exit_blocks = Set{Int}()
    for (from, exit_blk, _) in exit_edges
        if exit_blk ∉ redirected_exit_blocks
            push!(redirected_exit_blocks, exit_blk)
            # Replace return with goto latch
            exit_bb = ir.cfg.blocks[exit_blk]
            for esi in first(exit_bb.stmts):last(exit_bb.stmts)
                if ir.stmts.stmt[esi] isa ReturnNode
                    ir.stmts.stmt[esi] = GotoNode(bbl_idx)
                end
            end
            # Update CFG: exit_block now goes to latch
            push!(exit_bb.succs, bbl_idx)
            push!(bbl.preds, exit_blk)
        end
    end

    # --- Update multiplexer phis: remove old back-edge entries, add latch entry ---
    for phi_si in [disc_si; collect(values(phi_ssa_map))]
        stmt = ir.stmts.stmt[phi_si]
        stmt isa PhiNode || continue
        # Build new phi: keep external entries (not from back-edge sources), add latch
        new_edges = Int32[]; new_values = Any[]
        back_sources = Set{Int}(from for (from, _) in back_edges)
        for (idx, edge) in enumerate(stmt.edges)
            if Int(edge) ∉ back_sources
                push!(new_edges, edge)
                push!(new_values, isassigned(stmt.values, idx) ? stmt.values[idx] : Undef(ir.stmts.type[phi_si]))
            end
        end
        # Add latch edge with the latch's corresponding phi
        push!(new_edges, Int32(bbl_idx))
        if phi_si == disc_si
            push!(new_values, SSAValue(latch_disc_si))
        else
            # Find the latch carry phi for this mux phi
            mux_phis_sorted = sort(collect(phi_ssa_map), by=first)
            carry_idx = findfirst(p -> p[2] == phi_si, mux_phis_sorted)
            push!(new_values, SSAValue(latch_carry_sis[carry_idx]))
        end
        ir.stmts.stmt[phi_si] = PhiNode(new_edges, new_values)
    end

    return ir
end

"""Append a statement to the IR's instruction stream."""
function append_stmt!(ir::IRCode, si::Int, @nospecialize(stmt), @nospecialize(typ))
    push!(ir.stmts.stmt, stmt)
    push!(ir.stmts.type, typ)
    push!(ir.stmts.info, NoCallInfo())
    push!(ir.stmts.line, Int32(0))
    push!(ir.stmts.flag, UInt32(0))
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
