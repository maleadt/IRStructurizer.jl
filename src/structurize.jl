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
    line_map::Dict{Int, Int}    # ssa_idx → anchor PC/linetable index
end

function StructurizeCtx(ir::IRCode, line_map::Dict{Int, Int}=Dict{Int, Int}())
    domtree = construct_domtree(ir)
    postdomtree = construct_postdomtree(ir)
    loops = compute_natural_loops(ir, domtree)
    n = length(ir.stmts.stmt)
    # `ctx.types` feeds only structural positions (op result / block-arg / Undef
    # types), which must be concrete `Type`s. Widen so a lattice element (e.g.
    # `Core.Const` on a phi with one literal edge) can't land there; statement
    # types copied verbatim by the walk keep their original `ir.stmts.type`.
    types = Any[widenconst(t) for t in ir.stmts.type]
    StructurizeCtx(ir, domtree, postdomtree, loops, n + 1, 1, types, Dict{Int,Int}(), line_map)
end

alloc_ssa!(ctx::StructurizeCtx) = (idx = ctx.next_ssa; ctx.next_ssa += 1; idx)
alloc_arg!(ctx::StructurizeCtx) = (id = ctx.next_arg; ctx.next_arg += 1; id)

"""Map a synthesized SSA index to the same source location as an existing SSA index."""
function anchor_line!(ctx::StructurizeCtx, new_ssa::Int, source_ssa::Int)
    haskey(ctx.line_map, source_ssa) || return
    ctx.line_map[new_ssa] = source_ssa  # positive anchor → follow to resolve
end

"""Remap SSAValue references in a statement. Clones Expr to avoid mutating shared IRCode."""
function remap_stmt(@nospecialize(stmt), remap::Dict{Int, Int})
    isempty(remap) && return stmt
    if stmt isa SSAValue
        return remap_ssa_ref(stmt, remap)
    elseif stmt isa Expr
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

# CFG analysis: natural loop detection + irreducible CFG normalization
include("structurize/cfg.jl")

# Core walk: structurize_region!, emit_branch!, resolve_dest
include("structurize/walk.jl")

# Loop/branch analysis: find_branch_regions, emit_loop!, extract phis
include("structurize/loops.jl")

#=============================================================================
 Entry Point
=============================================================================#

"""
    structurize(ir::IRCode, line_map) -> (Block, max_ssa, max_arg, line_map)

Convert flat IRCode into a structured Block with nested IfOp/LoopOp/WhileOp/ForOp.
"""
function structurize(ir::IRCode, line_map::Dict{Int, Int}=Dict{Int, Int}())
    check_irreducible(ir)
    ctx = StructurizeCtx(ir, line_map)
    all_blocks = Set(1:length(ir.cfg.blocks))
    entry = structurize_region!(ctx, 1, all_blocks)
    promote_loops!(entry, ctx)
    return entry, ctx.next_ssa - 1, ctx.next_arg - 1, ctx.line_map
end
