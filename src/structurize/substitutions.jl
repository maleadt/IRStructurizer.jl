# SSA substitution machinery for structurization (phi refs → block args)
#
# These functions accept any context with `next_arg::Int` field for allocating
# BlockArgument IDs (duck-typed to work with StructurizeCtx).

#=============================================================================
 SSA Substitution (phi refs → block args)
=============================================================================#

"""
    Substitutions

A mapping from SSA value indices to BlockArguments.
Used during IR construction to replace phi node references with block arguments.
"""
const Substitutions = Dict{Int, BlockArgument}

"""
    substitute_ssa(value, subs::Substitutions)

Recursively substitute SSAValues with BlockArguments according to the substitution map.
Used to convert phi node references to block argument references inside loop bodies.
"""
function substitute_ssa(value, subs::Substitutions)
    if value isa SSAValue && haskey(subs, value.id)
        return subs[value.id]
    elseif value isa Expr
        new_args = Any[substitute_ssa(a, subs) for a in value.args]
        return Expr(value.head, new_args...)
    elseif value isa PiNode
        return PiNode(substitute_ssa(value.val, subs), value.typ)
    elseif value isa PhiNode
        # Phi nodes shouldn't appear in structured IR, but handle gracefully
        new_values = Vector{Any}(undef, length(value.values))
        for i in eachindex(value.values)
            if isassigned(value.values, i)
                new_values[i] = substitute_ssa(value.values[i], subs)
            end
        end
        return PhiNode(value.edges, new_values)
    else
        return value
    end
end

# Convenience for empty substitutions
substitute_ssa(value) = value

#=============================================================================
 Block Substitution (apply SSA → BlockArgument mappings)
=============================================================================#

"""
    apply_substitutions!(block::Block, subs::Substitutions, ctx)

Apply SSA substitutions within a block. Does not recurse into control flow regions.
Each control flow op's entry values (condition, init_values) are substituted,
but the nested regions are handled by process_block_args! dispatch.

`ctx` must have a mutable `next_arg::Int` field for allocating BlockArgument IDs.
"""
function apply_substitutions!(block::Block, subs::Substitutions, ctx)
    isempty(subs) && return

    new_body = SSAMap()
    for (idx, entry) in block.body
        if entry.stmt isa ControlFlowOp
            apply_substitutions!(entry.stmt, subs, ctx)
            push!(new_body, (idx, entry.stmt, entry.typ))
        else
            new_expr = substitute_ssa(entry.stmt, subs)
            push!(new_body, (idx, new_expr, entry.typ))
        end
    end
    block.body = new_body

    if block.terminator !== nothing
        block.terminator = substitute_terminator(block.terminator, subs)
    end
end

function apply_substitutions!(op::IfOp, subs::Substitutions, ctx)
    op.condition = substitute_ssa(op.condition, subs)
    apply_substitutions!(op.then_region, subs, ctx)
    apply_substitutions!(op.else_region, subs, ctx)
end

function apply_substitutions!(op::ForOp, subs::Substitutions, ctx)
    # Substitute bounds and init_values (evaluated in outer scope)
    op.lower = substitute_ssa(op.lower, subs)
    op.upper = substitute_ssa(op.upper, subs)
    op.step = substitute_ssa(op.step, subs)
    for (j, v) in enumerate(op.init_values)
        op.init_values[j] = substitute_ssa(v, subs)
    end

    # Thread outer BlockArguments through inner loop as invariant carries.
    isempty(subs) && return
    inner_subs = Substitutions()
    for (ssa_idx, outer_arg) in subs
        inner_arg = BlockArgument(alloc_arg!(ctx), outer_arg.type)
        push!(op.body.args, inner_arg)
        push!(op.init_values, outer_arg)
        if op.body.terminator isa ContinueOp
            push!(op.body.terminator.values, inner_arg)
        end
        inner_subs[ssa_idx] = inner_arg
    end
    apply_substitutions!(op.body, inner_subs, ctx)
end

function apply_substitutions!(op::LoopOp, subs::Substitutions, ctx)
    for (j, v) in enumerate(op.init_values)
        op.init_values[j] = substitute_ssa(v, subs)
    end

    isempty(subs) && return
    inner_subs = Substitutions()
    for (ssa_idx, outer_arg) in subs
        inner_arg = BlockArgument(alloc_arg!(ctx), outer_arg.type)
        push!(op.body.args, inner_arg)
        push!(op.init_values, outer_arg)
        thread_loop_carry!(op.body, inner_arg)
        inner_subs[ssa_idx] = inner_arg
    end
    apply_substitutions!(op.body, inner_subs, ctx)
end

"""
    thread_loop_carry!(block, inner_arg)

Push `inner_arg` to every ContinueOp and BreakOp terminator reachable from `block`,
recursing into nested IfOps (but not into nested loop ops, which have their own scopes).
"""
function thread_loop_carry!(block::Block, inner_arg::BlockArgument)
    if block.terminator isa ContinueOp
        push!(block.terminator.values, inner_arg)
    elseif block.terminator isa BreakOp
        push!(block.terminator.values, inner_arg)
    end
    for stmt in statements(block.body)
        if stmt isa IfOp
            thread_loop_carry!(stmt.then_region, inner_arg)
            thread_loop_carry!(stmt.else_region, inner_arg)
        end
    end
end

function apply_substitutions!(op::WhileOp, subs::Substitutions, ctx)
    for (j, v) in enumerate(op.init_values)
        op.init_values[j] = substitute_ssa(v, subs)
    end

    isempty(subs) && return
    before_subs = Substitutions()
    after_subs = Substitutions()
    for (ssa_idx, outer_arg) in subs
        # before region
        before_arg = BlockArgument(alloc_arg!(ctx), outer_arg.type)
        push!(op.before.args, before_arg)
        push!(op.init_values, outer_arg)
        if op.before.terminator isa ConditionOp
            push!(op.before.terminator.args, before_arg)
        end

        # after region
        after_arg = BlockArgument(alloc_arg!(ctx), outer_arg.type)
        push!(op.after.args, after_arg)
        if op.after.terminator isa YieldOp
            push!(op.after.terminator.values, after_arg)
        end

        before_subs[ssa_idx] = before_arg
        after_subs[ssa_idx] = after_arg
    end
    apply_substitutions!(op.before, before_subs, ctx)
    apply_substitutions!(op.after, after_subs, ctx)
end


"""
    substitute_terminator(term, subs::Substitutions)

Apply SSA substitutions to a terminator's values.
"""
function substitute_terminator(term::ContinueOp, subs::Substitutions)
    new_values = [substitute_ssa(v, subs) for v in term.values]
    return ContinueOp(new_values)
end

function substitute_terminator(term::BreakOp, subs::Substitutions)
    new_values = [substitute_ssa(v, subs) for v in term.values]
    return BreakOp(new_values)
end

function substitute_terminator(term::ConditionOp, subs::Substitutions)
    new_cond = substitute_ssa(term.condition, subs)
    new_args = [substitute_ssa(v, subs) for v in term.args]
    return ConditionOp(new_cond, new_args)
end

function substitute_terminator(term::YieldOp, subs::Substitutions)
    new_values = [substitute_ssa(v, subs) for v in term.values]
    return YieldOp(new_values)
end

function substitute_terminator(term::ReturnNode, subs::Substitutions)
    if isdefined(term, :val)
        new_val = substitute_ssa(term.val, subs)
        if new_val !== term.val
            return ReturnNode(new_val)
        end
    end
    return term
end

function substitute_terminator(term::Nothing, subs::Substitutions)
    return nothing
end
