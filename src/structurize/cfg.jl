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
 Irreducible CFG Detection
=============================================================================#

"""
    check_irreducible(ir::IRCode)

Detect irreducible control flow (multi-entry SCCs) and throw
`UnstructuredControlFlowError` if found. Julia IR is almost always reducible;
irreducible CFGs arise only from `@goto`.
"""
function check_irreducible(ir::IRCode)
    domtree = construct_domtree(ir)
    reach = CFGReachability(ir.cfg, domtree)
    for bb in 1:length(ir.cfg.blocks)
        if bb_in_irreducible_loop(reach, bb)
            throw(UnstructuredControlFlowError(
                "irreducible control flow detected at BB$bb — " *
                "multi-entry cycles (e.g. from @goto) are not supported"))
        end
    end
end
