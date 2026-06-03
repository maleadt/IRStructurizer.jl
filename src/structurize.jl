# CFGToSCF-style structurization, after MLIR's CFGToSCF (Bahmann et al. 2015):
#   Phase 1: lift cycles to LoopOps (via natural loop detection)
#   Phase 2: lift branches to IfOps (via dominance-based region splitting)
# Both phases recurse until no unstructured CF remains. A post-pass promotes
# LoopOps to WhileOp/ForOp where possible.

#=============================================================================
 Context
=============================================================================#

mutable struct StructurizeCtx
    m::Any                       # the MCFG (untyped: MCFG is defined in multiplex.jl,
                                 # included after this file; annotate `ctx.m::MCFG` locally)
    cfg::CFG                     # build_cfg(m), cached (block index == MBlock id)
    domtree::DomTree
    # header => set of block indices in the natural loop
    loop_map::Dict{Int, Set{Int}}
    next_ssa::Int
    next_arg::Int
    types::Dict{Int, Any}       # ssa id => widened type (block args + body stmts + synthesized)
    def_block::Dict{Int, Int}   # ssa id => defining MBlock id (block args + body stmts)
    ssa_remap::Dict{Int, Int}   # original => fresh (for inner defs)
    line_map::Dict{Int, Int}    # ssa_idx => anchor PC/linetable index
end

function StructurizeCtx(m, line_map::Dict{Int, Int}=Dict{Int, Int}())
    cfg = build_cfg(m)
    domtree = construct_domtree(cfg)
    loops = natural_loops_m(m)
    # `ctx.types` feeds structural positions (op result / block-arg / Undef types),
    # which must be concrete `Type`s. Widen so a lattice element (e.g. `Core.Const`
    # on a single-literal-edge arg) can't land there. Block-arg and synthesized
    # types live in `m.types`; body-statement types live in each `MStmt`.
    types = Dict{Int, Any}()
    def_block = Dict{Int, Int}()
    for (id, t) in m.types
        types[id] = widenconst(t)
    end
    for (bid, b) in enumerate(m.blocks)
        for a in b.args
            def_block[a] = bid
        end
        for s in b.body
            types[s.id] = widenconst(s.type)
            def_block[s.id] = bid
        end
    end
    StructurizeCtx(m, cfg, domtree, loops, m.next_id, 1, types, def_block,
                   Dict{Int,Int}(), line_map)
end

alloc_ssa!(ctx::StructurizeCtx) = (idx = ctx.next_ssa; ctx.next_ssa += 1; idx)
alloc_arg!(ctx::StructurizeCtx) = (id = ctx.next_arg; ctx.next_arg += 1; id)

"""Map a synthesized SSA index to the same source location as an existing SSA index."""
function anchor_line!(ctx::StructurizeCtx, new_ssa::Int, source_ssa::Int)
    haskey(ctx.line_map, source_ssa) || return
    ctx.line_map[new_ssa] = source_ssa  # positive anchor: follow to resolve
end

"""
    remap_ssa(stmt, f) -> stmt

Rebuild `stmt` with every value operand passed through `f` (a value-mapping
closure). The SSA-substitution primitive shared by `remap_stmt` (the walk),
`emit` (multiplex), and `assemble_ircode` (unstructurize); each supplies its own
`f`. Handles every operand-bearing node: `Expr`, `PiNode`, `PhiNode` (unassigned
slots left unassigned), `GotoIfNot` (cond), `ReturnNode` (val), and a bare
`SSAValue`. Clones rather than mutates, so shared IR is safe.
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
    structurize(m::MCFG, line_map; promote=true) -> (Block, max_ssa, max_arg, line_map)

Convert the (already-normalized) explicit-edge `MCFG` into a structured Block with
nested IfOp/LoopOp/WhileOp/ForOp. The lift reads the `MBlock` form directly: block
arguments and per-edge operands replace Julia phi nodes.

The core walk emits only the generic `LoopOp`; `WhileOp`/`ForOp` recognition lives
in the `promote_loops!` post-pass. Pass `promote=false` to get the pre-promotion
form, where every loop is a `LoopOp`.
"""
function structurize(m, line_map::Dict{Int, Int}=Dict{Int, Int}();
                     promote::Bool=true)
    ctx = StructurizeCtx(m, line_map)
    all_blocks = Set(1:length(ctx.m.blocks))
    entry = structurize_region!(ctx, ctx.m.entry, all_blocks)
    promote && promote_loops!(entry, ctx)
    return entry, ctx.next_ssa - 1, ctx.next_arg - 1, ctx.line_map
end

"""
    lift_mcfg(m::MCFG; validate=true, promote=true) -> StructuredIRCode

Lift a normalized `MCFG` to a `StructuredIRCode`. `split_duplicate_edges!` first
routes any `GotoIfNot` whose two edges target the same block through a trampoline,
so every predecessor reaches a block by at most one edge (the lift reads "what
predecessor P contributes" as a single edge operand; a `cond ? a : b` shape needs
the two predecessors distinct). Debug info comes from the `MBlock` codelocs.
"""
function lift_mcfg(m::MCFG; validate::Bool=true, promote::Bool=true)
    split_duplicate_edges!(m)
    debuginfo_table, line_map = capture_debuginfo(m)
    valid_worlds = m.valid_worlds isa WorldRange ? m.valid_worlds :
                   WorldRange(typemin(UInt), typemax(UInt))
    sci = StructuredIRCode(copy(m.argtypes), copy(m.sptypes), Block(), 0, 0,
                           debuginfo_table, line_map, valid_worlds)
    entry, max_ssa, max_arg, updated_line_map = structurize(m, line_map; promote)
    sci.entry = entry
    sci.max_ssa_idx = max_ssa
    sci.max_arg_idx = max_arg
    merge!(sci.line_map, updated_line_map)

    # Parent chain (entry to SCI, sub-blocks to containing block) after structurize
    # and promote, since promote_loops! replaces block.body without going through
    # push!.
    sci.entry.parent = sci
    fix_parents!(sci.entry)

    if validate
        validate_scf(sci.entry)
        validate_no_phis(sci.entry)
        validate_terminators(sci)
        validate_ssa_defs(sci)
        validate_ssa_uniqueness(sci)
    end
    return sci
end
