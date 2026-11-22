# Convert StructuredIRCode back to flat IRCode.
#
# Lowers nested control flow ops (IfOp, ForOp, WhileOp, LoopOp, TryOp) back to
# GotoNode/GotoIfNot/PhiNode/ReturnNode (and EnterNode/:leave/PhiCNode) for
# execution via OpaqueClosure.


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
    header_carry_phis::Vector{PhiNode}      # carry phis
    exit_phis::Vector{PhiNode}              # for BreakOp (LoopOp only)
    break_gotos::Vector{Tuple{Int, Int}}    # (bb, stmt_pos) of GotoNode(-1) placeholders
end

struct TryTarget
    enter_ssa::Int                          # sparse SSA of the EnterNode
    merge_phis::Vector{PhiNode}             # the TryOp's results
    exit_gotos::Vector{Tuple{Int, Int}}     # (bb, stmt_pos) of GotoNode(-1) placeholders
end

mutable struct UnstructurizeCtx
    bbs::Vector{FlatBB}
    next_ssa::Int
    ssa_rename::Dict{Int, Int}               # old structured IR SSA → sparse SSA
    arg_rename::Dict{Int, Int}               # BlockArgument.id → sparse SSA of phi
    cfop_results::Dict{Int, Vector{Int}}     # cfop old SSA → result phi sparse SSAs
    loop_stack::Vector{LoopTarget}
    try_stack::Vector{TryTarget}             # enclosing TryOp bodies (innermost last)
    # maps sparse SSA → debug-info anchor (same semantics as StructurizeCtx.line_map)
    line_map::Dict{Int, Int}
end

function UnstructurizeCtx(line_map::Dict{Int, Int}=Dict{Int, Int}())
    UnstructurizeCtx(FlatBB[], 0, Dict{Int,Int}(), Dict{Int,Int}(),
                     Dict{Int,Vector{Int}}(), LoopTarget[], TryTarget[],
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
 Value Resolution (structured IR values to sparse SSA)
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
    elseif stmt isa Core.UpsilonNode
        isdefined(stmt, :val) || return stmt
        return Core.UpsilonNode(resolve_value(ctx, stmt.val))
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
    propagate_line!(ctx, sparse, old_ssa)
    return sparse
end

# Anchor line info from a structured IR SSA index onto a sparse SSA. Resolve to
# the final negative value immediately to avoid cycles: sparse SSA indices can
# overlap with old structured SSA indices in the same line_map.
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
            error("internal error: ForOp at %$idx reached lowering; expand_for_loops! runs first")
        elseif stmt isa WhileOp
            bb = lower_whileop!(ctx, bb, idx, stmt, typ)
        elseif stmt isa LoopOp
            bb = lower_loopop!(ctx, bb, idx, stmt, typ)
        elseif stmt isa TryOp
            bb = lower_tryop!(ctx, bb, idx, stmt, typ)
        elseif is_cfop_getfield(ctx, stmt)
            cfop_old = stmt.args[2].id
            field_idx = stmt.args[3]::Int
            ctx.ssa_rename[idx] = ctx.cfop_results[cfop_old][field_idx]
        elseif stmt isa Undef
            emit_undef!(ctx, bb, idx, typ)
        else
            emit_resolved!(ctx, bb, idx, stmt, typ)
        end
    end
    return bb
end

"""Define `old_ssa` as undefined. Julia IR has no undef value, only a phi that has
no value for the edge taken, so emit an empty `PhiNode` after the block's leading
phis."""
function emit_undef!(ctx::UnstructurizeCtx, bb::Int, old_ssa::Int, @nospecialize(typ))
    stmts = ctx.bbs[bb].stmts
    ssa = alloc_ssa!(ctx)
    pos = something(findfirst(s -> !(s[2] isa PhiNode), stmts), length(stmts) + 1)
    insert!(stmts, pos, (ssa, PhiNode(Int32[], Any[]), typ))
    ctx.ssa_rename[old_ssa] = ssa
    propagate_line!(ctx, ssa, old_ssa)
    return ssa
end

#=============================================================================
 IfOp Lowering
=============================================================================#

function lower_ifop!(ctx::UnstructurizeCtx, bb::Int, cfop_idx::Int,
                     op::IfOp, @nospecialize(cfop_typ))
    cond = resolve_value(ctx, op.condition)

    # GotoIfNot with placeholder dest, fixed up after the then-region
    branch_ssa = emit!(ctx, bb, GotoIfNot(cond, -1), Any)
    anchor_sparse_line!(ctx, branch_ssa, cfop_idx)
    branch_pos = length(ctx.bbs[bb].stmts)

    # then_bb is next in sequence, the fallthrough taken when cond is true
    then_bb = new_bb!(ctx)
    then_last = lower_block_body!(ctx, then_bb, op.then_region)
    then_term = op.then_region.terminator

    else_bb = new_bb!(ctx)
    fix_branch_dest!(ctx, bb, branch_pos, cond, else_bb)

    else_last = lower_block_body!(ctx, else_bb, op.else_region)
    else_term = op.else_region.terminator

    # which branches yield, vs return/continue/break
    then_yields = then_term isa YieldOp
    else_yields = else_term isa YieldOp

    if then_yields || else_yields
        # At least one branch yields, so a merge block is needed. Lower the other
        # branch's exit first: a LeaveOp adds blocks, and the merge must stay the
        # last block, where the code after the IfOp falls through.
        then_yields || lower_diverging_terminator!(ctx, then_last, then_term)
        else_yields || lower_diverging_terminator!(ctx, else_last, else_term)
        merge_bb = new_bb!(ctx)
        then_yields && emit!(ctx, then_last, GotoNode(merge_bb), Any)
        else_yields && emit!(ctx, else_last, GotoNode(merge_bb), Any)

        # build the merge PhiNodes
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
        # both branches diverge (return/continue/break)
        lower_diverging_terminator!(ctx, then_last, then_term)
        lower_diverging_terminator!(ctx, else_last, else_term)
        ctx.cfop_results[cfop_idx] = Int[]
        # unreachable merge block for any code that follows the IfOp
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
    elseif term isa LeaveOp
        handle_leave!(ctx, bb, term.values)
    elseif term === nothing
        # unreachable block, nothing to emit
    else
        error("Unexpected diverging terminator: $(typeof(term))")
    end
end

function handle_continue!(ctx::UnstructurizeCtx, bb::Int, term::ContinueOp)
    @assert !isempty(ctx.loop_stack) "ContinueOp outside loop"
    lt = ctx.loop_stack[end]

    # add carry values to the header phis
    for (i, phi) in enumerate(lt.header_carry_phis)
        val = resolve_value(ctx, term.values[i])
        push_phi_value!(phi, bb, val)
    end

    emit!(ctx, bb, GotoNode(lt.header_bb), Any)
end

function handle_break!(ctx::UnstructurizeCtx, bb::Int, term::BreakOp)
    @assert !isempty(ctx.loop_stack) "BreakOp outside loop"
    lt = ctx.loop_stack[end]

    # add values to the exit phis
    for (i, phi) in enumerate(lt.exit_phis)
        val = resolve_value(ctx, term.values[i])
        push_phi_value!(phi, bb, val)
    end

    # placeholder GotoNode; exit_bb is not known until the loop is fully lowered
    pos = length(ctx.bbs[bb].stmts) + 1
    emit!(ctx, bb, GotoNode(-1), Any)
    push!(lt.break_gotos, (bb, pos))
end

#=============================================================================
 TryOp Lowering
=============================================================================#

"""Lower a `TryOp`: an `EnterNode` ending `bb`, the body falling through from it,
the handler as the catch block (its arguments become `PhiCNode`s over the
upsilons), and a merge block whose phis are the op's results. Every exit from the
body pops the handler with an explicit `:leave` (`handle_leave!`)."""
function lower_tryop!(ctx::UnstructurizeCtx, bb::Int, cfop_idx::Int,
                      op::TryOp, @nospecialize(cfop_typ))
    scope = has_scope(op) ? resolve_value(ctx, op.scope) : nothing

    # EnterNode placeholder ending `bb`, patched once the catch block exists.
    # `pop_exception` statements name the TryOp, i.e. this enter.
    enter_ssa = emit!(ctx, bb, nothing, Any)
    enter_pos = length(ctx.bbs[bb].stmts)
    ctx.ssa_rename[cfop_idx] = enter_ssa
    anchor_sparse_line!(ctx, enter_ssa, cfop_idx)

    n_results = cfop_typ isa DataType && cfop_typ <: Tuple ? length(cfop_typ.parameters) : 0
    result_types = extract_tuple_types(cfop_typ, n_results)
    tt = TryTarget(enter_ssa, PhiNode[PhiNode(Int32[], Any[]) for _ in 1:n_results],
                   Tuple{Int,Int}[])

    # body_bb is next in sequence: the enter's fallthrough
    body_bb = new_bb!(ctx)
    push!(ctx.try_stack, tt)
    body_last = lower_block_body!(ctx, body_bb, op.body)
    body_term = op.body.terminator
    if body_term isa Union{YieldOp, LeaveOp}
        handle_leave!(ctx, body_last, body_term.values)
    else
        lower_diverging_terminator!(ctx, body_last, body_term)
    end
    pop!(ctx.try_stack)

    catch_bb = 0
    if op.handler !== nothing
        catch_bb = new_bb!(ctx)
        for (k, arg) in enumerate(op.handler.args)
            vals = Any[resolve_value(ctx, SSAValue(u)) for u in op.upsilons[k]]
            ctx.arg_rename[arg.id] = emit!(ctx, catch_bb, Core.PhiCNode(vals), arg.type)
        end
        handler_last = lower_block_body!(ctx, catch_bb, op.handler)
        handler_term = op.handler.terminator
        if handler_term isa YieldOp
            # The handler already runs with the handler popped: no :leave.
            goto_try_merge!(ctx, handler_last, tt, handler_term.values)
        else
            lower_diverging_terminator!(ctx, handler_last, handler_term)
        end
    end
    old = ctx.bbs[bb].stmts[enter_pos]
    enter = has_scope(op) ? Core.EnterNode(catch_bb, scope) : Core.EnterNode(catch_bb)
    ctx.bbs[bb].stmts[enter_pos] = (old[1], enter, old[3])

    merge_bb = new_bb!(ctx)
    phi_ssas = Int[]
    for (i, phi) in enumerate(tt.merge_phis)
        ssa = emit!(ctx, merge_bb, phi, result_types[i])
        anchor_sparse_line!(ctx, ssa, cfop_idx)
        push!(phi_ssas, ssa)
    end
    for (b, pos) in tt.exit_gotos
        old = ctx.bbs[b].stmts[pos]
        ctx.bbs[b].stmts[pos] = (old[1], GotoNode(merge_bb), old[3])
    end
    ctx.cfop_results[cfop_idx] = phi_ssas
    return merge_bb
end

"""Leave the innermost enclosing TryOp body from `bb` with `values` as its results.
Julia ends a block at each `:leave`, so `bb` jumps to a fresh block holding only
the leave, which falls through into the jump to the merge (filled in by
`lower_tryop!`)."""
function handle_leave!(ctx::UnstructurizeCtx, bb::Int, values::Vector{IRValue})
    @assert !isempty(ctx.try_stack) "LeaveOp outside a TryOp body"
    tt = ctx.try_stack[end]
    leave_bb = new_bb!(ctx)
    emit!(ctx, bb, GotoNode(leave_bb), Any)
    emit!(ctx, leave_bb, Expr(:leave, SSAValue(tt.enter_ssa)), Any)
    goto_try_merge!(ctx, new_bb!(ctx), tt, values)
end

function goto_try_merge!(ctx::UnstructurizeCtx, bb::Int, tt::TryTarget,
                         values::Vector{IRValue})
    for (i, phi) in enumerate(tt.merge_phis)
        push_phi_value!(phi, bb, resolve_value(ctx, values[i]))
    end
    emit!(ctx, bb, GotoNode(-1), Any)
    push!(tt.exit_gotos, (bb, length(ctx.bbs[bb].stmts)))
end

#=============================================================================
 WhileOp Lowering
=============================================================================#

function lower_whileop!(ctx::UnstructurizeCtx, bb::Int, cfop_idx::Int,
                        op::WhileOp, @nospecialize(cfop_typ))
    header_bb = new_bb!(ctx)
    emit!(ctx, bb, GotoNode(header_bb), Any)

    # header PhiNodes for carries
    carry_phis = PhiNode[]
    carry_phi_ssas = Int[]
    for (i, init_val) in enumerate(op.init_values)
        phi = PhiNode(Int32[], Any[])
        push_phi_value!(phi, bb, resolve_value(ctx, init_val))
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

    # lower the before-region body (condition computation)
    header_last = lower_block_body!(ctx, header_bb, op.before)

    # ConditionOp becomes GotoIfNot
    cond_term = op.before.terminator::ConditionOp
    cond = resolve_value(ctx, cond_term.condition)

    # GotoIfNot with placeholder exit
    emit!(ctx, header_last, GotoIfNot(cond, -1), Any)
    branch_pos = length(ctx.bbs[header_last].stmts)

    # after_bb is next in sequence, the fallthrough taken when cond is true
    after_bb = new_bb!(ctx)

    # A ContinueOp nested in an IfOp arm of the after region (an expanded
    # exclusive ForOp with a conditional continuation) is a back edge of this loop.
    lt = LoopTarget(header_bb, Ref(-1), carry_phis, PhiNode[], Tuple{Int,Int}[])
    push!(ctx.loop_stack, lt)
    after_last = lower_block_body!(ctx, after_bb, op.after)
    pop!(ctx.loop_stack)

    # YieldOp becomes the back-edge to the header
    yield_term = op.after.terminator::YieldOp
    for (i, phi) in enumerate(carry_phis)
        val = resolve_value(ctx, yield_term.values[i])
        push_phi_value!(phi, after_last, val)
    end
    emit!(ctx, after_last, GotoNode(header_bb), Any)

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

    # header PhiNodes for carries
    carry_phis = PhiNode[]
    carry_phi_ssas = Int[]
    for (i, init_val) in enumerate(op.init_values)
        phi = PhiNode(Int32[], Any[])
        push_phi_value!(phi, bb, resolve_value(ctx, init_val))
        carry_arg = op.body.args[i]
        phi_ssa = emit!(ctx, header_bb, phi, carry_arg.type)
        ctx.arg_rename[carry_arg.id] = phi_ssa
        push!(carry_phis, phi)
        push!(carry_phi_ssas, phi_ssa)
    end

    # pre-create exit phis (BreakOps add edges during body lowering); the result
    # count comes from cfop_typ
    result_types = extract_tuple_types(cfop_typ,
        cfop_typ isa DataType && cfop_typ <: Tuple ? length(cfop_typ.parameters) : 0)
    exit_phis = PhiNode[PhiNode(Int32[], Any[]) for _ in result_types]

    lt = LoopTarget(header_bb, Ref(-1), carry_phis, exit_phis,
                    Tuple{Int,Int}[])
    push!(ctx.loop_stack, lt)

    # lower the body into header_bb
    body_last = lower_block_body!(ctx, header_bb, op.body)

    body_term = op.body.terminator
    if body_term !== nothing
        lower_diverging_terminator!(ctx, body_last, body_term)
    end

    pop!(ctx.loop_stack)

    # create exit_bb, emit exit phis, fix break placeholders
    exit_bb = new_bb!(ctx)
    lt.exit_bb_ref[] = exit_bb

    exit_phi_ssas = Int[]
    for (i, phi) in enumerate(exit_phis)
        ssa = emit!(ctx, exit_bb, phi, result_types[i])
        push!(exit_phi_ssas, ssa)
    end

    for (b, pos) in lt.break_gotos
        old = ctx.bbs[b].stmts[pos]
        ctx.bbs[b].stmts[pos] = (old[1], GotoNode(exit_bb), old[3])
    end

    ctx.cfop_results[cfop_idx] = exit_phi_ssas
    return exit_bb
end

#=============================================================================
 Assembly: flatten BBs into IRCode
=============================================================================#

function assemble_ircode(ctx::UnstructurizeCtx, sci::StructuredIRCode)
    # ensure every BB has at least one statement
    for i in 1:length(ctx.bbs)
        if isempty(ctx.bbs[i].stmts)
            emit!(ctx, i, nothing, Nothing)
        end
    end

    # map each sparse SSA to its final contiguous position
    sparse_to_final = Dict{Int, Int}()
    pos = 0
    for bb in ctx.bbs
        for (sparse_ssa, _, _) in bb.stmts
            pos += 1
            sparse_to_final[sparse_ssa] = pos
        end
    end
    n = pos

    function remap_val(@nospecialize(val))
        if val isa SSAValue
            return SSAValue(sparse_to_final[val.id])
        else
            return val  # Argument, GlobalRef, constants, etc.
        end
    end

    # Build flat statement/type arrays. BB indices in Goto*/Phi edges are
    # unchanged; remap_ssa only rewrites value operands via remap_val.
    all_stmts = Vector{Any}(undef, n)
    all_types = Vector{Any}(undef, n)
    pos = 0
    for bb in ctx.bbs
        for (_, stmt, typ) in bb.stmts
            pos += 1
            all_stmts[pos] = remap_ssa(stmt, remap_val)
            all_types[pos] = typ
        end
    end

    # debug info: fill `line` from the per-statement line_map
    @static if VERSION >= v"1.12-"
        line = fill(Int32(0), n * 3)
        if sci.debuginfo_table !== nothing
            pos = 0
            for bb in ctx.bbs
                for (sparse_ssa, _, _) in bb.stmts
                    pos += 1
                    pc = resolve_line(ctx.line_map, sparse_ssa)
                    pc === nothing && continue
                    # Preserve the raw edge id/pc; the debuginfo traversal API
                    # resolves the edge but does not expose those indices.
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

    # per-block statement ranges (every BB has >=1 stmt, ensured above)
    bb_ranges = UnitRange{Int}[]
    offset = 0
    for bb in ctx.bbs
        len = length(bb.stmts)
        push!(bb_ranges, (offset + 1):(offset + len))
        offset += len
    end

    return build_dense_ircode(all_stmts, all_types, fill(UInt32(0), n), line, bb_ranges;
                              argtypes=sci.argtypes, sptypes=sci.sptypes,
                              debuginfo=sci.debuginfo_table,
                              valid_worlds=sci.valid_worlds)
end

function _cfg_edge!(blocks::Vector{BasicBlock}, from::Int, to::Int)
    push!(blocks[to].preds, from)
    push!(blocks[from].succs, to)
end

"""
    build_dense_ircode(all_stmts, all_types, all_flags, line, bb_ranges;
                       argtypes, sptypes, debuginfo, valid_worlds) -> IRCode

Assemble a dense `IRCode` from flat statement arrays plus per-block statement
ranges. Builds the CFG (preds/succs from each block's last statement), the
`InstructionStream`, and the debug info, then constructs the `IRCode`.
"""
function build_dense_ircode(all_stmts, all_types, all_flags, line, bb_ranges;
                            argtypes, sptypes, debuginfo,
                            valid_worlds::WorldRange=WorldRange(typemin(UInt), typemax(UInt)))
    n = length(all_stmts)
    nb = length(bb_ranges)
    bb_blocks = BasicBlock[]
    cfg_index = Int[]                       # first stmt of blocks 2..nb (length nb-1)
    for (i, r) in enumerate(bb_ranges)
        push!(bb_blocks, BasicBlock(StmtRange(first(r), last(r)), Int[], Int[]))
        i > 1 && push!(cfg_index, first(r))
    end
    for (i, r) in enumerate(bb_ranges)
        last_s = all_stmts[last(r)]
        if last_s isa GotoNode
            _cfg_edge!(bb_blocks, i, last_s.label)
        elseif last_s isa GotoIfNot
            _cfg_edge!(bb_blocks, i, last_s.dest)
            i < nb && _cfg_edge!(bb_blocks, i, i + 1)
        elseif last_s isa ReturnNode
            # no successors
        elseif last_s isa Core.EnterNode
            # As `compute_basic_blocks`: the catch block gets the exceptional edge
            # plus a virtual edge from outside the function (pred 0).
            if last_s.catch_dest != 0
                _cfg_edge!(bb_blocks, i, last_s.catch_dest)
                push!(bb_blocks[last_s.catch_dest].preds, 0)
            end
            i < nb && _cfg_edge!(bb_blocks, i, i + 1)
        else
            i < nb && _cfg_edge!(bb_blocks, i, i + 1)
        end
    end
    cfg = CFG(bb_blocks, cfg_index)

    info = Vector{CC.CallInfo}(undef, n)
    fill!(info, CC.NoCallInfo())
    stmts = InstructionStream(all_stmts, all_types, info, line, all_flags)
    meta = Expr[]

    @static if VERSION >= v"1.12-"
        di = CC.DebugInfoStream(line)
        if debuginfo isa CC.DebugInfoStream
            di.def = debuginfo.def
            di.linetable = debuginfo.linetable
            di.edges = copy(debuginfo.edges)
        end
        return IRCode(stmts, cfg, di, copy(argtypes), meta, CC.VarState[s for s in sptypes],
                      valid_worlds)
    else
        # 1.11's IRCode has no valid_worlds field; the SCI-captured range is
        # only used for binding-partition lookups there.
        linetable = debuginfo isa Vector ? copy(debuginfo) : Core.LineInfoNode[]
        return IRCode(stmts, cfg, linetable, copy(argtypes), meta, CC.VarState[s for s in sptypes])
    end
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
    if has_forop(sci)
        sci = expand_for_loops!(copy(sci))
    end
    ctx = UnstructurizeCtx(copy(sci.line_map))
    bb = new_bb!(ctx)
    bb = lower_block_body!(ctx, bb, sci.entry)

    term = sci.entry.terminator
    if term isa ReturnNode
        emit!(ctx, bb, resolve_stmt(ctx, term), Any)
    elseif term !== nothing
        error("Unexpected entry block terminator: $(typeof(term))")
    end

    return assemble_ircode(ctx, sci)
end

