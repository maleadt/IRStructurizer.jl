# Unstructurize: convert StructuredIRCode back to flat IRCode
#
# Lowers nested control flow ops (IfOp, ForOp, WhileOp, LoopOp) back to
# GotoNode/GotoIfNot/PhiNode/ReturnNode for execution via OpaqueClosure.

const CC = Core.Compiler

#=============================================================================
 Data Structures
=============================================================================#

mutable struct FlatBB
    stmts::Vector{Tuple{Int, Any, Any}}  # (sparse_ssa, stmt, type)
end
FlatBB() = FlatBB(Tuple{Int, Any, Any}[])

struct LoopTarget
    header_bb::Int
    exit_bb_ref::Ref{Int}                   # set after body lowering (-1 = placeholder)
    header_carry_phis::Vector{PhiNode}       # carry phis (excluding IV for ForOp)
    iv_info::Union{Nothing, @NamedTuple{phi::PhiNode, ssa::Int, step::Any, typ::Any}}
    exit_phis::Vector{PhiNode}               # for BreakOp (LoopOp only)
    break_gotos::Vector{Tuple{Int, Int}}     # (bb, stmt_pos) of GotoNode(-1) placeholders
end

mutable struct UnstructurizeCtx
    bbs::Vector{FlatBB}
    next_ssa::Int
    ssa_rename::Dict{Int, Int}               # old structured IR SSA → sparse SSA
    arg_rename::Dict{Int, Int}               # BlockArgument.id → sparse SSA of phi
    cfop_results::Dict{Int, Vector{Int}}     # cfop old SSA → result phi sparse SSAs
    loop_stack::Vector{LoopTarget}
    # Debug info: maps sparse SSA → anchor (same semantics as StructurizeCtx.line_map)
    line_map::Dict{Int, Int}
end

function UnstructurizeCtx(line_map::Dict{Int, Int}=Dict{Int, Int}())
    UnstructurizeCtx(FlatBB[], 0, Dict{Int,Int}(), Dict{Int,Int}(),
                     Dict{Int,Vector{Int}}(), LoopTarget[],
                     line_map)
end

#=============================================================================
 BB & SSA Helpers
=============================================================================#

function new_bb!(ctx::UnstructurizeCtx)
    push!(ctx.bbs, FlatBB())
    return length(ctx.bbs)
end

function alloc_ssa!(ctx::UnstructurizeCtx)
    ctx.next_ssa += 1
    return ctx.next_ssa
end

function emit!(ctx::UnstructurizeCtx, bb::Int, @nospecialize(stmt), @nospecialize(typ))
    ssa = alloc_ssa!(ctx)
    push!(ctx.bbs[bb].stmts, (ssa, stmt, typ))
    return ssa
end

#=============================================================================
 Value Resolution (structured IR values → sparse SSA)
=============================================================================#

function resolve_value(ctx::UnstructurizeCtx, @nospecialize(val))
    if val isa SSAValue
        haskey(ctx.ssa_rename, val.id) ||
            error("SSAValue %$(val.id) not found in ssa_rename")
        return SSAValue(ctx.ssa_rename[val.id])
    elseif val isa BlockArgument
        haskey(ctx.arg_rename, val.id) ||
            error("BlockArgument @$(val.id) not found in arg_rename")
        return SSAValue(ctx.arg_rename[val.id])
    elseif val isa Undef
        return val
    else
        return val  # Argument, GlobalRef, QuoteNode, literals, etc.
    end
end

function resolve_stmt(ctx::UnstructurizeCtx, @nospecialize(stmt))
    if stmt isa Expr
        return Expr(stmt.head, Any[resolve_value(ctx, a) for a in stmt.args]...)
    elseif stmt isa Core.PiNode
        return Core.PiNode(resolve_value(ctx, stmt.val), stmt.typ)
    elseif stmt isa ReturnNode
        isdefined(stmt, :val) || return stmt
        return ReturnNode(resolve_value(ctx, stmt.val))
    elseif stmt isa SSAValue || stmt isa BlockArgument
        return resolve_value(ctx, stmt)
    else
        return stmt  # nothing, constants, GlobalRef, etc.
    end
end

function emit_resolved!(ctx::UnstructurizeCtx, bb::Int, old_ssa::Int,
                        @nospecialize(stmt), @nospecialize(typ))
    resolved = resolve_stmt(ctx, stmt)
    sparse = emit!(ctx, bb, resolved, typ)
    ctx.ssa_rename[old_ssa] = sparse
    # Propagate debug info: old_ssa → sparse
    propagate_line!(ctx, sparse, old_ssa)
    return sparse
end

# Propagate/anchor line info between structured IR SSA indices and sparse SSAs.
# Resolve to the final negative value immediately to avoid cycles (sparse SSA
# indices can overlap with old structured SSA indices in the same line_map).
function propagate_line!(ctx::UnstructurizeCtx, sparse_ssa::Int, old_ssa::Int)
    val = resolve_line(ctx.line_map, old_ssa)
    val !== nothing && (ctx.line_map[sparse_ssa] = -val)
end
function anchor_sparse_line!(ctx::UnstructurizeCtx, sparse_ssa::Int, source_old_ssa::Int)
    val = resolve_line(ctx.line_map, source_old_ssa)
    val !== nothing && (ctx.line_map[sparse_ssa] = -val)
end

#=============================================================================
 PhiNode Construction (handles Undef by leaving slots unassigned)
=============================================================================#

function push_phi_value!(phi::PhiNode, bb::Int, @nospecialize(val))
    push!(phi.edges, Int32(bb))
    if val isa Undef
        resize!(phi.values, length(phi.values) + 1)
        # leave unassigned
    else
        push!(phi.values, val)
    end
end

#=============================================================================
 getfield Detection
=============================================================================#

function is_cfop_getfield(ctx::UnstructurizeCtx, @nospecialize(stmt))
    stmt isa Expr || return false
    stmt.head === :call || return false
    length(stmt.args) == 3 || return false
    stmt.args[1] === Core.getfield || return false
    stmt.args[2] isa SSAValue || return false
    return haskey(ctx.cfop_results, stmt.args[2].id)
end

#=============================================================================
 Block Body Lowering
=============================================================================#

"""
    lower_block_body!(ctx, bb, block) -> Int

Lower a structured IR Block's body into flat BBs. Returns the last BB used
(may differ from `bb` if control flow ops created new BBs).
"""
function lower_block_body!(ctx::UnstructurizeCtx, bb::Int, block::Block)
    for (idx, entry) in block.body
        stmt, typ = entry.stmt, entry.type
        if stmt isa IfOp
            bb = lower_ifop!(ctx, bb, idx, stmt, typ)
        elseif stmt isa ForOp
            bb = lower_forop!(ctx, bb, idx, stmt, typ)
        elseif stmt isa WhileOp
            bb = lower_whileop!(ctx, bb, idx, stmt, typ)
        elseif stmt isa LoopOp
            bb = lower_loopop!(ctx, bb, idx, stmt, typ)
        elseif is_cfop_getfield(ctx, stmt)
            cfop_old = stmt.args[2].id
            field_idx = stmt.args[3]::Int
            ctx.ssa_rename[idx] = ctx.cfop_results[cfop_old][field_idx]
        else
            emit_resolved!(ctx, bb, idx, stmt, typ)
        end
    end
    return bb
end

#=============================================================================
 IfOp Lowering
=============================================================================#

function lower_ifop!(ctx::UnstructurizeCtx, bb::Int, cfop_idx::Int,
                     op::IfOp, @nospecialize(cfop_typ))
    cond = resolve_value(ctx, op.condition)

    # Emit GotoIfNot with placeholder dest (fixed after then-region)
    branch_ssa = emit!(ctx, bb, GotoIfNot(cond, -1), Any)
    anchor_sparse_line!(ctx, branch_ssa, cfop_idx)
    branch_pos = length(ctx.bbs[bb].stmts)

    # then_bb is next in sequence → correct fallthrough for GotoIfNot
    then_bb = new_bb!(ctx)
    then_last = lower_block_body!(ctx, then_bb, op.then_region)
    then_term = op.then_region.terminator

    # Create else_bb and fix placeholder
    else_bb = new_bb!(ctx)
    fix_branch_dest!(ctx, bb, branch_pos, cond, else_bb)

    else_last = lower_block_body!(ctx, else_bb, op.else_region)
    else_term = op.else_region.terminator

    # Check which branches yield (vs return/continue/break)
    then_yields = then_term isa YieldOp
    else_yields = else_term isa YieldOp

    if then_yields || else_yields
        # At least one branch yields → need merge block
        merge_bb = new_bb!(ctx)

        if then_yields
            emit!(ctx, then_last, GotoNode(merge_bb), Any)
        else
            lower_diverging_terminator!(ctx, then_last, then_term)
        end
        if else_yields
            emit!(ctx, else_last, GotoNode(merge_bb), Any)
        else
            lower_diverging_terminator!(ctx, else_last, else_term)
        end

        # Create merge PhiNodes
        phi_ssas = Int[]
        then_vals = then_yields ? then_term.values : nothing
        else_vals = else_yields ? else_term.values : nothing
        n_results = something(
            then_vals !== nothing ? length(then_vals) : nothing,
            else_vals !== nothing ? length(else_vals) : nothing,
            0)

        result_types = extract_tuple_types(cfop_typ, n_results)

        for i in 1:n_results
            phi = PhiNode(Int32[], Any[])
            if then_vals !== nothing
                push_phi_value!(phi, then_last, resolve_value(ctx, then_vals[i]))
            end
            if else_vals !== nothing
                push_phi_value!(phi, else_last, resolve_value(ctx, else_vals[i]))
            end
            ssa = emit!(ctx, merge_bb, phi, result_types[i])
            anchor_sparse_line!(ctx, ssa, cfop_idx)
            push!(phi_ssas, ssa)
        end

        ctx.cfop_results[cfop_idx] = phi_ssas
        return merge_bb
    else
        # Both branches diverge (return/continue/break)
        lower_diverging_terminator!(ctx, then_last, then_term)
        lower_diverging_terminator!(ctx, else_last, else_term)
        ctx.cfop_results[cfop_idx] = Int[]
        # Unreachable merge block for any code that follows the IfOp
        return new_bb!(ctx)
    end
end

function fix_branch_dest!(ctx::UnstructurizeCtx, bb::Int, pos::Int,
                          @nospecialize(cond), dest::Int)
    old = ctx.bbs[bb].stmts[pos]
    ctx.bbs[bb].stmts[pos] = (old[1], GotoIfNot(cond, dest), old[3])
end

function extract_tuple_types(@nospecialize(typ), n::Int)
    if typ isa DataType && typ <: Tuple && length(typ.parameters) == n
        return Any[p for p in typ.parameters]
    else
        return fill(Any, n)
    end
end

#=============================================================================
 Diverging Terminator Handling (ReturnNode, ContinueOp, BreakOp)
=============================================================================#

function lower_diverging_terminator!(ctx::UnstructurizeCtx, bb::Int,
                                     @nospecialize(term))
    if term isa ReturnNode
        emit!(ctx, bb, resolve_stmt(ctx, term), Any)
    elseif term isa ContinueOp
        handle_continue!(ctx, bb, term)
    elseif term isa BreakOp
        handle_break!(ctx, bb, term)
    elseif term === nothing
        # unreachable block — do nothing
    else
        error("Unexpected diverging terminator: $(typeof(term))")
    end
end

function handle_continue!(ctx::UnstructurizeCtx, bb::Int, term::ContinueOp)
    @assert !isempty(ctx.loop_stack) "ContinueOp outside loop"
    lt = ctx.loop_stack[end]

    # ForOp: synthesize IV increment
    if lt.iv_info !== nothing
        iv = lt.iv_info
        iv_next = emit!(ctx, bb,
            Expr(:call, GlobalRef(Core.Intrinsics, :add_int),
                 SSAValue(iv.ssa), iv.step),
            iv.typ)
        push_phi_value!(iv.phi, bb, SSAValue(iv_next))
    end

    # Add carry values to header phis
    for (i, phi) in enumerate(lt.header_carry_phis)
        val = resolve_value(ctx, term.values[i])
        push_phi_value!(phi, bb, val)
    end

    emit!(ctx, bb, GotoNode(lt.header_bb), Any)
end

function handle_break!(ctx::UnstructurizeCtx, bb::Int, term::BreakOp)
    @assert !isempty(ctx.loop_stack) "BreakOp outside loop"
    lt = ctx.loop_stack[end]

    # Add values to exit phis
    for (i, phi) in enumerate(lt.exit_phis)
        val = resolve_value(ctx, term.values[i])
        push_phi_value!(phi, bb, val)
    end

    # Emit placeholder GotoNode (exit_bb not yet known)
    pos = length(ctx.bbs[bb].stmts) + 1
    emit!(ctx, bb, GotoNode(-1), Any)
    push!(lt.break_gotos, (bb, pos))
end

#=============================================================================
 ForOp Lowering
=============================================================================#

function lower_forop!(ctx::UnstructurizeCtx, bb::Int, cfop_idx::Int,
                      op::ForOp, @nospecialize(cfop_typ))
    lower = resolve_value(ctx, op.lower)
    upper = resolve_value(ctx, op.upper)
    step  = resolve_value(ctx, op.step)

    header_bb = new_bb!(ctx)
    emit!(ctx, bb, GotoNode(header_bb), Any)

    # Header PhiNodes: IV + carries
    iv_phi = PhiNode(Int32[bb], Any[lower])
    iv_phi_ssa = emit!(ctx, header_bb, iv_phi, op.iv_arg.type)
    ctx.arg_rename[op.iv_arg.id] = iv_phi_ssa

    carry_phis = PhiNode[]
    carry_phi_ssas = Int[]
    for (i, init_val) in enumerate(op.init_values)
        init_resolved = resolve_value(ctx, init_val)
        phi = PhiNode(Int32[bb], Any[init_resolved])
        carry_arg = op.body.args[i]
        phi_ssa = emit!(ctx, header_bb, phi, carry_arg.type)
        ctx.arg_rename[carry_arg.id] = phi_ssa
        push!(carry_phis, phi)
        push!(carry_phi_ssas, phi_ssa)
    end

    # Condition: slt_int(iv, upper)
    cond_ssa = emit!(ctx, header_bb,
        Expr(:call, GlobalRef(Core.Intrinsics, :slt_int),
             SSAValue(iv_phi_ssa), upper),
        Bool)

    # GotoIfNot with placeholder exit
    emit!(ctx, header_bb, GotoIfNot(SSAValue(cond_ssa), -1), Any)
    branch_pos = length(ctx.bbs[header_bb].stmts)

    # body_bb: next in sequence (fallthrough)
    body_bb = new_bb!(ctx)

    # Set up loop target
    iv_info = (; phi=iv_phi, ssa=iv_phi_ssa, step=step, typ=op.iv_arg.type)
    lt = LoopTarget(header_bb, Ref(-1), carry_phis, iv_info, PhiNode[],
                    Tuple{Int,Int}[])
    push!(ctx.loop_stack, lt)

    body_last = lower_block_body!(ctx, body_bb, op.body)

    # Handle body terminator
    body_term = op.body.terminator
    if body_term isa ContinueOp
        handle_continue!(ctx, body_last, body_term)
    else
        lower_diverging_terminator!(ctx, body_last, body_term)
    end

    pop!(ctx.loop_stack)

    # Create exit_bb and fix placeholder
    exit_bb = new_bb!(ctx)
    fix_branch_dest!(ctx, header_bb, branch_pos, SSAValue(cond_ssa), exit_bb)

    ctx.cfop_results[cfop_idx] = carry_phi_ssas
    return exit_bb
end

#=============================================================================
 WhileOp Lowering
=============================================================================#

function lower_whileop!(ctx::UnstructurizeCtx, bb::Int, cfop_idx::Int,
                        op::WhileOp, @nospecialize(cfop_typ))
    header_bb = new_bb!(ctx)
    emit!(ctx, bb, GotoNode(header_bb), Any)

    # Header PhiNodes for carries
    carry_phis = PhiNode[]
    carry_phi_ssas = Int[]
    for (i, init_val) in enumerate(op.init_values)
        init_resolved = resolve_value(ctx, init_val)
        phi = PhiNode(Int32[bb], Any[init_resolved])
        carry_arg = op.before.args[i]
        phi_ssa = emit!(ctx, header_bb, phi, carry_arg.type)
        ctx.arg_rename[carry_arg.id] = phi_ssa
        # after.args share the same BlockArgument IDs
        if i <= length(op.after.args)
            ctx.arg_rename[op.after.args[i].id] = phi_ssa
        end
        push!(carry_phis, phi)
        push!(carry_phi_ssas, phi_ssa)
    end

    # Lower before-region body (condition computation)
    header_last = lower_block_body!(ctx, header_bb, op.before)

    # ConditionOp → GotoIfNot
    cond_term = op.before.terminator::ConditionOp
    cond = resolve_value(ctx, cond_term.condition)

    # GotoIfNot with placeholder exit
    emit!(ctx, header_last, GotoIfNot(cond, -1), Any)
    branch_pos = length(ctx.bbs[header_last].stmts)

    # after_bb: next in sequence (fallthrough when cond is true)
    after_bb = new_bb!(ctx)

    # Lower after-region body
    after_last = lower_block_body!(ctx, after_bb, op.after)

    # YieldOp → back-edge to header
    yield_term = op.after.terminator::YieldOp
    for (i, phi) in enumerate(carry_phis)
        val = resolve_value(ctx, yield_term.values[i])
        push_phi_value!(phi, after_last, val)
    end
    emit!(ctx, after_last, GotoNode(header_bb), Any)

    # Create exit_bb and fix placeholder
    exit_bb = new_bb!(ctx)
    fix_branch_dest!(ctx, header_last, branch_pos, cond, exit_bb)

    ctx.cfop_results[cfop_idx] = carry_phi_ssas
    return exit_bb
end

#=============================================================================
 LoopOp Lowering
=============================================================================#

function lower_loopop!(ctx::UnstructurizeCtx, bb::Int, cfop_idx::Int,
                       op::LoopOp, @nospecialize(cfop_typ))
    header_bb = new_bb!(ctx)
    emit!(ctx, bb, GotoNode(header_bb), Any)

    # Header PhiNodes for carries
    carry_phis = PhiNode[]
    carry_phi_ssas = Int[]
    for (i, init_val) in enumerate(op.init_values)
        init_resolved = resolve_value(ctx, init_val)
        phi = PhiNode(Int32[bb], Any[init_resolved])
        carry_arg = op.body.args[i]
        phi_ssa = emit!(ctx, header_bb, phi, carry_arg.type)
        ctx.arg_rename[carry_arg.id] = phi_ssa
        push!(carry_phis, phi)
        push!(carry_phi_ssas, phi_ssa)
    end

    # Pre-create exit phis (BreakOps add edges during body lowering)
    n_results = length(extract_tuple_types(cfop_typ, 0))
    # Use cfop_typ to determine result count
    result_types = extract_tuple_types(cfop_typ,
        cfop_typ isa DataType && cfop_typ <: Tuple ? length(cfop_typ.parameters) : 0)
    exit_phis = PhiNode[PhiNode(Int32[], Any[]) for _ in result_types]

    lt = LoopTarget(header_bb, Ref(-1), carry_phis, nothing, exit_phis,
                    Tuple{Int,Int}[])
    push!(ctx.loop_stack, lt)

    # Lower body into header_bb
    body_last = lower_block_body!(ctx, header_bb, op.body)

    # Handle body terminator
    body_term = op.body.terminator
    if body_term !== nothing
        lower_diverging_terminator!(ctx, body_last, body_term)
    end

    pop!(ctx.loop_stack)

    # Create exit_bb, emit exit phis, fix break placeholders
    exit_bb = new_bb!(ctx)
    lt.exit_bb_ref[] = exit_bb

    exit_phi_ssas = Int[]
    for (i, phi) in enumerate(exit_phis)
        ssa = emit!(ctx, exit_bb, phi, result_types[i])
        push!(exit_phi_ssas, ssa)
    end

    # Fix break goto placeholders
    for (b, pos) in lt.break_gotos
        old = ctx.bbs[b].stmts[pos]
        ctx.bbs[b].stmts[pos] = (old[1], GotoNode(exit_bb), old[3])
    end

    ctx.cfop_results[cfop_idx] = exit_phi_ssas
    return exit_bb
end

#=============================================================================
 Assembly: flatten BBs → IRCode
=============================================================================#

function assemble_ircode(ctx::UnstructurizeCtx, sci::StructuredIRCode)
    # Ensure all BBs have at least one statement
    for i in 1:length(ctx.bbs)
        if isempty(ctx.bbs[i].stmts)
            emit!(ctx, i, nothing, Nothing)
        end
    end

    # Build sparse_ssa → final_position mapping
    sparse_to_final = Dict{Int, Int}()
    pos = 0
    for bb in ctx.bbs
        for (sparse_ssa, _, _) in bb.stmts
            pos += 1
            sparse_to_final[sparse_ssa] = pos
        end
    end
    n = pos

    # Value remapping: sparse SSA → final contiguous index
    function remap_val(@nospecialize(val))
        if val isa SSAValue
            return SSAValue(sparse_to_final[val.id])
        else
            return val  # Argument, GlobalRef, constants, etc.
        end
    end

    function remap_stmt(@nospecialize(stmt))
        if stmt isa Expr
            return Expr(stmt.head, Any[remap_val(a) for a in stmt.args]...)
        elseif stmt isa PhiNode
            new_edges = copy(stmt.edges)  # BB indices unchanged
            new_values = Vector{Any}(undef, length(stmt.values))
            for i in 1:length(stmt.values)
                if isassigned(stmt.values, i)
                    new_values[i] = remap_val(stmt.values[i])
                end
            end
            return PhiNode(new_edges, new_values)
        elseif stmt isa GotoNode
            return stmt  # BB indices unchanged
        elseif stmt isa GotoIfNot
            return GotoIfNot(remap_val(stmt.cond), stmt.dest)
        elseif stmt isa ReturnNode
            isdefined(stmt, :val) || return stmt
            return ReturnNode(remap_val(stmt.val))
        elseif stmt isa Core.PiNode
            return Core.PiNode(remap_val(stmt.val), stmt.typ)
        elseif stmt isa SSAValue
            return remap_val(stmt)
        else
            return stmt  # nothing, constants, etc.
        end
    end

    # Build flat statement/type arrays
    all_stmts = Vector{Any}(undef, n)
    all_types = Vector{Any}(undef, n)
    pos = 0
    for bb in ctx.bbs
        for (_, stmt, typ) in bb.stmts
            pos += 1
            all_stmts[pos] = remap_stmt(stmt)
            all_types[pos] = typ
        end
    end

    # Build InstructionStream with debug info
    info = Vector{CC.CallInfo}(undef, n)
    fill!(info, CC.NoCallInfo())
    @static if VERSION >= v"1.12-"
        line = fill(Int32(0), n * 3)
        if sci.debuginfo_table !== nothing
            pos = 0
            for bb in ctx.bbs
                for (sparse_ssa, _, _) in bb.stmts
                    pos += 1
                    pc = resolve_line(ctx.line_map, sparse_ssa)
                    pc === nothing && continue
                    codeloc = CC.getdebugidx(sci.debuginfo_table, pc)
                    off = 3*(pos-1)
                    line[off+1] = codeloc[1]
                    line[off+2] = codeloc[2]
                    line[off+3] = codeloc[3]
                end
            end
        end
    else
        line = fill(Int32(0), n)
        if sci.debuginfo_table !== nothing
            pos = 0
            for bb in ctx.bbs
                for (sparse_ssa, _, _) in bb.stmts
                    pos += 1
                    li = resolve_line(ctx.line_map, sparse_ssa)
                    li !== nothing && (line[pos] = Int32(li))
                end
            end
        end
    end
    flag = fill(UInt32(0), n)
    stmts = InstructionStream(all_stmts, all_types, info, line, flag)

    # Build CFG
    bb_blocks = BasicBlock[]
    cfg_index = Int[]
    offset = 0
    for (i, bb) in enumerate(ctx.bbs)
        len = length(bb.stmts)
        push!(bb_blocks, BasicBlock(StmtRange(offset + 1, offset + len), Int[], Int[]))
        push!(cfg_index, offset + 1)
        offset += len
    end

    # Compute preds/succs from terminators
    for (i, bb) in enumerate(ctx.bbs)
        isempty(bb.stmts) && continue
        last_s = all_stmts[last(bb_blocks[i].stmts)]
        if last_s isa GotoNode
            _cfg_edge!(bb_blocks, i, last_s.label)
        elseif last_s isa GotoIfNot
            _cfg_edge!(bb_blocks, i, last_s.dest)
            if i < length(bb_blocks)
                _cfg_edge!(bb_blocks, i, i + 1)
            end
        elseif last_s isa ReturnNode
            # no successors
        else
            if i < length(bb_blocks)
                _cfg_edge!(bb_blocks, i, i + 1)
            end
        end
    end

    cfg = CFG(bb_blocks, cfg_index)

    argtypes = copy(sci.argtypes)
    sptypes = CC.VarState[s for s in sci.sptypes]
    meta = Expr[]

    @static if VERSION >= v"1.12-"
        debuginfo = CC.DebugInfoStream(stmts.line)
        if sci.debuginfo_table !== nothing
            orig = sci.debuginfo_table::CC.DebugInfoStream
            debuginfo.def = orig.def
            debuginfo.linetable = orig.linetable
            debuginfo.edges = copy(orig.edges)
        end
        return IRCode(stmts, cfg, debuginfo, argtypes, meta, sptypes)
    else
        linetable = if sci.debuginfo_table isa Vector
            copy(sci.debuginfo_table)
        else
            Core.LineInfoNode[]
        end
        return IRCode(stmts, cfg, linetable, argtypes, meta, sptypes)
    end
end

function _cfg_edge!(blocks::Vector{BasicBlock}, from::Int, to::Int)
    push!(blocks[to].preds, from)
    push!(blocks[from].succs, to)
end

#=============================================================================
 Public API
=============================================================================#

"""
    IRCode(sci::StructuredIRCode)

Convert a StructuredIRCode back to flat Julia IRCode with explicit control flow
(GotoNode, GotoIfNot, PhiNode, ReturnNode).
"""
function CC.IRCode(sci::StructuredIRCode)
    ctx = UnstructurizeCtx(copy(sci.line_map))
    bb = new_bb!(ctx)
    bb = lower_block_body!(ctx, bb, sci.entry)

    # Handle entry block terminator
    term = sci.entry.terminator
    if term isa ReturnNode
        emit!(ctx, bb, resolve_stmt(ctx, term), Any)
    elseif term !== nothing
        error("Unexpected entry block terminator: $(typeof(term))")
    end

    return assemble_ircode(ctx, sci)
end


