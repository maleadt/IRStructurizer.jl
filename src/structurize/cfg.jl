#=============================================================================
 Natural loop lookup

 Natural loops are detected on the MBlock CFG by `natural_loops_m` (multiplex.jl)
 and cached in `ctx.loop_map` (header id → in-loop block ids). Irreducible
 (multi-entry) loops are normalized away upstream by `normalize_cf!` (an entry
 multiplexer collapses each to a single-entry loop), so the lift only ever sees
 reducible, single-entry loops.
=============================================================================#

"""Return the innermost loop at `header` that is contained within `region_blocks`, or nothing."""
function get_loop_at(ctx::StructurizeCtx, header::Int, region_blocks::Set{Int})
    body = get(ctx.loop_map, header, nothing)
    body === nothing && return nothing
    # Only consider loops fully contained in the region
    issubset(body, region_blocks) || return nothing
    return body
end
