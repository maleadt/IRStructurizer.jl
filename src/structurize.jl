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

"""
    remap_ssa(stmt, f) -> stmt

Rebuild `stmt` with every value operand passed through `f` (a value-mapping
closure). The single SSA-substitution primitive shared by the walk
(`remap_stmt`), `emit` (multiplex), and `assemble_ircode` (unstructurize) — each
supplies its own `f`. Handles every operand-bearing node: `Expr`, `PiNode`,
`PhiNode` (unassigned slots left unassigned), `GotoIfNot` (cond), `ReturnNode`
(val), and a bare `SSAValue`. Clones rather than mutates, so shared IR is safe.
"""
function remap_ssa(@nospecialize(stmt), f)
    if stmt isa Expr
        return Expr(stmt.head, Any[f(a) for a in stmt.args]...)
    elseif stmt isa PiNode
        return PiNode(f(stmt.val), stmt.typ)
    elseif stmt isa PhiNode
        new_vals = Vector{Any}(undef, length(stmt.values))
        for k in eachindex(stmt.values)
            isassigned(stmt.values, k) && (new_vals[k] = f(stmt.values[k]))
        end
        return PhiNode(copy(stmt.edges), new_vals)
    elseif stmt isa GotoIfNot
        return GotoIfNot(f(stmt.cond), stmt.dest)
    elseif stmt isa ReturnNode
        return isdefined(stmt, :val) ? ReturnNode(f(stmt.val)) : stmt
    elseif stmt isa SSAValue
        return f(stmt)
    else
        return stmt
    end
end

"""Remap SSAValue references in a statement via an index map. Clones to avoid
mutating shared IRCode; identity (no allocation) when `remap` is empty."""
remap_stmt(@nospecialize(stmt), remap::Dict{Int, Int}) =
    isempty(remap) ? stmt : remap_ssa(stmt, v -> remap_ssa_ref(v, remap))

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
    structurize(ir::IRCode, line_map; promote=true) -> (Block, max_ssa, max_arg, line_map)

Convert flat IRCode into a structured Block with nested IfOp/LoopOp/WhileOp/ForOp.

The core walk emits only the generic `LoopOp` (invariant I6); `WhileOp`/`ForOp`
recognition lives entirely in the `promote_loops!` post-pass. Pass `promote=false`
to get the pre-promotion form (every loop is a `LoopOp`) — used to test I6.
"""
function structurize(ir::IRCode, line_map::Dict{Int, Int}=Dict{Int, Int}();
                     promote::Bool=true)
    check_irreducible(ir)
    ctx = StructurizeCtx(ir, line_map)
    all_blocks = Set(1:length(ir.cfg.blocks))
    entry = structurize_region!(ctx, 1, all_blocks)
    promote && promote_loops!(entry, ctx)
    return entry, ctx.next_ssa - 1, ctx.next_arg - 1, ctx.line_map
end
