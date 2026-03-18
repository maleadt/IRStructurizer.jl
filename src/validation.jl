# structured IR validation

export UnstructuredControlFlowError, UnsubstitutedPhiError, InvalidTerminatorError,
       UndefinedSSAError

"""
Exception thrown when unstructured control flow is detected in structured IR.
"""
struct UnstructuredControlFlowError <: Exception
    stmt_indices::Vector{Int}
end

function Base.showerror(io::IO, e::UnstructuredControlFlowError)
    print(io, "UnstructuredControlFlowError: unstructured control flow at statement(s): ",
          join(e.stmt_indices, ", "))
end

"""
Exception thrown when phi nodes remain after block arg substitution.
"""
struct UnsubstitutedPhiError <: Exception
    stmt_indices::Vector{Int}
end

function Base.showerror(io::IO, e::UnsubstitutedPhiError)
    print(io, "UnsubstitutedPhiError: phi nodes remain at statement(s): ",
          join(e.stmt_indices, ", "))
end

"""
    validate_scf(entry::Block) -> Bool

Validate that all control flow has been converted to structured ops.
Throws `UnstructuredControlFlowError` if GotoNode/GotoIfNot remains.
"""
function validate_scf(entry::Block)
    unstructured = Int[]
    validate_no_gotos!(unstructured, entry)
    isempty(unstructured) || throw(UnstructuredControlFlowError(sort!(unstructured)))
    return true
end

validate_scf(sci::StructuredIRCode) = validate_scf(sci.entry)

function validate_no_gotos!(bad::Vector{Int}, block::Block)
    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa GotoNode || stmt isa GotoIfNot
            push!(bad, idx)
        elseif stmt isa IfOp
            validate_no_gotos!(bad, stmt.then_region)
            validate_no_gotos!(bad, stmt.else_region)
        elseif stmt isa LoopOp
            validate_no_gotos!(bad, stmt.body)
        end
    end
end

"""
    validate_no_phis(entry::Block) -> Bool

Validate that all phi nodes have been converted to BlockArgs.
Throws `UnsubstitutedPhiError` if PhiNode expressions remain.
"""
function validate_no_phis(entry::Block)
    remaining = Int[]
    validate_no_phis!(remaining, entry)
    isempty(remaining) || throw(UnsubstitutedPhiError(sort!(remaining)))
    return true
end

validate_no_phis(sci::StructuredIRCode) = validate_no_phis(sci.entry)

function validate_no_phis!(bad::Vector{Int}, block::Block)
    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa PhiNode
            push!(bad, idx)
        elseif stmt isa IfOp
            validate_no_phis!(bad, stmt.then_region)
            validate_no_phis!(bad, stmt.else_region)
        elseif stmt isa LoopOp
            validate_no_phis!(bad, stmt.body)
        end
    end
end

"""
Exception thrown when structured control flow ops have invalid terminators.
"""
struct InvalidTerminatorError <: Exception
    messages::Vector{String}
end

function Base.showerror(io::IO, e::InvalidTerminatorError)
    print(io, "InvalidTerminatorError: ")
    for (i, msg) in enumerate(e.messages)
        i > 1 && print(io, "; ")
        print(io, msg)
    end
end

"""
    validate_terminators(sci::StructuredIRCode) -> Bool

Validate that all structured control flow ops have correct terminators.
Throws `InvalidTerminatorError` if any terminator is missing or invalid.

Validation rules:
- IfOp: both regions must have explicit terminator (never `nothing`)
- ForOp body: must have ContinueOp
- WhileOp before: must have ConditionOp
- WhileOp after: must have YieldOp
- LoopOp body: recursively validate nested ops
"""
function validate_terminators(sci::StructuredIRCode)
    errors = String[]
    validate_terminators!(errors, sci, sci.entry)
    isempty(errors) || throw(InvalidTerminatorError(errors))
    return true
end

# Convenience method for testing: wrap block in minimal SCI
function validate_terminators(entry::Block)
    sci = StructuredIRCode(Any[], Any[], entry, 0)
    return validate_terminators(sci)
end

function validate_terminators!(errors::Vector{String}, sci::StructuredIRCode, block::Block)
    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa IfOp
            validate_if_terminators!(errors, sci, stmt, idx)
        elseif stmt isa ForOp
            validate_for_terminators!(errors, sci, stmt, idx)
        elseif stmt isa WhileOp
            validate_while_terminators!(errors, sci, stmt, idx)
        elseif stmt isa LoopOp
            validate_loop_terminators!(errors, sci, stmt, idx)
        end
    end
end

function validate_if_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::IfOp, idx::Int)
    then_term = op.then_region.terminator
    else_term = op.else_region.terminator

    # Both regions must have explicit terminators
    # Having `nothing` as terminator is always invalid for IfOp regions
    # Valid terminators: YieldOp, ReturnNode, ContinueOp, BreakOp (for IfOps inside loops)
    if then_term === nothing
        push!(errors, "IfOp at %$idx: then region must have explicit terminator, got nothing")
    end
    if else_term === nothing
        push!(errors, "IfOp at %$idx: else region must have explicit terminator, got nothing")
    end

    # Validate yield arity and types: both branches must yield same number of values with matching types
    if then_term isa YieldOp && else_term isa YieldOp
        then_arity = length(then_term.values)
        else_arity = length(else_term.values)
        if then_arity != else_arity
            push!(errors, "IfOp at %$idx: yield arity mismatch (then yields $then_arity, else yields $else_arity)")
        end

        # Type validation for matching positions
        for i in 1:min(then_arity, else_arity)
            then_type = resolve_type(sci, then_term.values[i])
            else_type = resolve_type(sci, else_term.values[i])
            if then_type !== nothing && else_type !== nothing && then_type != else_type
                push!(errors, "IfOp at %$idx: yield type mismatch at position $i (then: $then_type, else: $else_type)")
            end
        end
    end

    # Recursively validate nested ops
    validate_terminators!(errors, sci, op.then_region)
    validate_terminators!(errors, sci, op.else_region)
end

function validate_for_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::ForOp, idx::Int)
    term = op.body.terminator
    if !(term isa ContinueOp)
        push!(errors, "ForOp at %$idx: body must have ContinueOp, got $(typeof(term))")
    end

    # Recursively validate nested ops
    validate_terminators!(errors, sci, op.body)
end

function validate_while_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::WhileOp, idx::Int)
    before_term = op.before.terminator
    after_term = op.after.terminator

    if !(before_term isa ConditionOp)
        push!(errors, "WhileOp at %$idx: before region must have ConditionOp, got $(typeof(before_term))")
    end
    if !(after_term isa YieldOp)
        push!(errors, "WhileOp at %$idx: after region must have YieldOp, got $(typeof(after_term))")
    end

    # Recursively validate nested ops
    validate_terminators!(errors, sci, op.before)
    validate_terminators!(errors, sci, op.after)
end

function validate_loop_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::LoopOp, idx::Int)
    # LoopOp body can have various terminators (BreakOp, ContinueOp, etc.)
    # Just recursively validate nested ops
    validate_terminators!(errors, sci, op.body)
end

#=============================================================================
 SSA Definition Validation
=============================================================================#

"""
Exception thrown when SSA values are used but never defined in the structured IR.
"""
struct UndefinedSSAError <: Exception
    undefined::Vector{Int}
end

function Base.showerror(io::IO, e::UndefinedSSAError)
    print(io, "UndefinedSSAError: SSA values used but not defined: ",
          join(("%$id" for id in e.undefined), ", "))
end

"""
    validate_ssa_defs(sci::StructuredIRCode) -> Bool

Validate that all SSAValue references in the structured IR have definitions.
Collects all SSA ids defined in block bodies and all SSA ids referenced in
statements and terminators, then checks that every used id is defined.

Throws `UndefinedSSAError` if any SSAValue is used but never defined.
"""
function validate_ssa_defs(sci::StructuredIRCode)
    defs = Set{Int}()
    uses = Set{Int}()
    collect_ssa_defs_uses!(defs, uses, sci.entry)
    undefined = sort!(collect(setdiff(uses, defs)))
    isempty(undefined) || throw(UndefinedSSAError(undefined))
    return true
end

function collect_ssa_defs_uses!(defs::Set{Int}, uses::Set{Int}, block::Block)
    # Collect definitions and uses from body statements
    for (idx, entry) in block.body
        push!(defs, idx)
        collect_ssa_uses!(defs, uses, entry.stmt)
    end

    # Collect uses from terminator
    collect_terminator_uses!(uses, block.terminator)
end

# Collect SSAValue references from a statement (two-arg: non-nested statements)
function collect_ssa_uses!(::Set{Int}, ::Set{Int}, stmt)
    # Leaf types that don't reference SSAValues
end

function collect_ssa_uses!(::Set{Int}, uses::Set{Int}, val::SSAValue)
    push!(uses, val.id)
end

function collect_ssa_uses!(::Set{Int}, uses::Set{Int}, expr::Expr)
    for arg in expr.args
        arg isa SSAValue && push!(uses, arg.id)
    end
end

function collect_ssa_uses!(::Set{Int}, uses::Set{Int}, node::GotoIfNot)
    node.cond isa SSAValue && push!(uses, node.cond.id)
end

function collect_ssa_uses!(::Set{Int}, uses::Set{Int}, node::ReturnNode)
    if isdefined(node, :val) && node.val isa SSAValue
        push!(uses, node.val.id)
    end
end

function collect_ssa_uses!(defs::Set{Int}, uses::Set{Int}, op::IfOp)
    op.condition isa SSAValue && push!(uses, op.condition.id)
    collect_ssa_defs_uses!(defs, uses, op.then_region)
    collect_ssa_defs_uses!(defs, uses, op.else_region)
end

function collect_ssa_uses!(defs::Set{Int}, uses::Set{Int}, op::LoopOp)
    for v in op.init_values
        v isa SSAValue && push!(uses, v.id)
    end
    collect_ssa_defs_uses!(defs, uses, op.body)
end

function collect_ssa_uses!(defs::Set{Int}, uses::Set{Int}, op::WhileOp)
    for v in op.init_values
        v isa SSAValue && push!(uses, v.id)
    end
    collect_ssa_defs_uses!(defs, uses, op.before)
    collect_ssa_defs_uses!(defs, uses, op.after)
end

function collect_ssa_uses!(defs::Set{Int}, uses::Set{Int}, op::ForOp)
    op.lower isa SSAValue && push!(uses, op.lower.id)
    op.upper isa SSAValue && push!(uses, op.upper.id)
    op.step isa SSAValue && push!(uses, op.step.id)
    for v in op.init_values
        v isa SSAValue && push!(uses, v.id)
    end
    collect_ssa_defs_uses!(defs, uses, op.body)
end

# Collect SSAValue references from terminators
function collect_terminator_uses!(uses::Set{Int}, term)
    # nothing terminator or unrecognized — no uses
end

function collect_terminator_uses!(uses::Set{Int}, term::Union{YieldOp, ContinueOp, BreakOp})
    for v in term.values
        v isa SSAValue && push!(uses, v.id)
    end
end

function collect_terminator_uses!(uses::Set{Int}, term::ConditionOp)
    term.condition isa SSAValue && push!(uses, term.condition.id)
    for v in term.args
        v isa SSAValue && push!(uses, v.id)
    end
end

function collect_terminator_uses!(uses::Set{Int}, term::ReturnNode)
    if isdefined(term, :val) && term.val isa SSAValue
        push!(uses, term.val.id)
    end
end
