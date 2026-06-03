#=============================================================================
 Natural loop lookup

 Natural loops are detected on the MBlock CFG by `natural_loops_m` (multiplex.jl)
 and cached in `ctx.loop_map` (header id to in-loop block ids). Irreducible
 (multi-entry) loops are normalized away upstream by `normalize_cf!`, so the
 lift only ever sees reducible, single-entry loops.
=============================================================================#

"""Return the innermost loop at `header` contained within `region_blocks`, or nothing."""
function get_loop_at(ctx::StructurizeCtx, header::Int, region_blocks::Set{Int})
    body = get(ctx.loop_map, header, nothing)
    body === nothing && return nothing
    issubset(body, region_blocks) || return nothing
    return body
end
