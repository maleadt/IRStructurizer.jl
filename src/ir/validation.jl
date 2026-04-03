# structured IR validation

export UnstructuredControlFlowError

"""
Exception thrown when unstructured control flow is detected in structured IR.
"""
struct UnstructuredControlFlowError <: Exception
    msg::String
end

UnstructuredControlFlowError(stmt_indices::Vector{Int}) =
    UnstructuredControlFlowError("unstructured control flow at statement(s): " *
                                  join(stmt_indices, ", "))

function Base.showerror(io::IO, e::UnstructuredControlFlowError)
    print(io, "UnstructuredControlFlowError: ", e.msg)
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
        elseif stmt isa ControlFlowOp
            for b in blocks(stmt)
                validate_no_gotos!(bad, b)
            end
        end
    end
end

"""
    validate_no_phis(entry::Block) -> Bool

Validate that all phi nodes have been converted to BlockArguments.
Errors if PhiNode expressions remain (indicates a bug in structurization).
"""
function validate_no_phis(entry::Block)
    remaining = Int[]
    validate_no_phis!(remaining, entry)
    isempty(remaining) || error("internal error: phi nodes remain at statement(s): ",
                                  join(sort!(remaining), ", "))
    return true
end

validate_no_phis(sci::StructuredIRCode) = validate_no_phis(sci.entry)

function validate_no_phis!(bad::Vector{Int}, block::Block)
    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa PhiNode
            push!(bad, idx)
        elseif stmt isa ControlFlowOp
            for b in blocks(stmt)
                validate_no_phis!(bad, b)
            end
        end
    end
end

"""
    validate_terminators(sci::StructuredIRCode) -> Bool

Validate that all structured control flow ops have correct terminators.
Errors if any terminator is missing or invalid (indicates a bug in structurization).

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
    isempty(errors) || error("internal error: invalid terminators: ",
                              join(errors, "; "))
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

        # Type validation for matching positions (Undef matches any type)
        for i in 1:min(then_arity, else_arity)
            then_term.values[i] isa Undef && continue
            else_term.values[i] isa Undef && continue
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
    n_init = length(op.init_values)
    n_args = length(op.body.args)

    # init_values must match body.args
    if n_init != n_args
        push!(errors, "LoopOp at %$idx: init_values length ($n_init) != body.args length ($n_args)")
    end

    # Validate all reachable ContinueOps and BreakOps match loop-carry length
    for term in reachable_terminators(op.body)
        if term isa ContinueOp
            nc = length(term.values)
            nc == n_init || push!(errors, "LoopOp at %$idx: ContinueOp has $nc values, expected $n_init (loop-carry length)")
        elseif term isa BreakOp
            nb = length(term.values)
            nb == n_init || push!(errors, "LoopOp at %$idx: BreakOp has $nb values, expected $n_init (loop-carry length)")
        end
    end

    # Recursively validate nested ops
    validate_terminators!(errors, sci, op.body)
end

#=============================================================================
 SSA Definition Validation
=============================================================================#

"""
    validate_ssa_defs(sci::StructuredIRCode) -> Bool

Validate that all SSAValue references in the structured IR have definitions
visible in their scope. Uses scope-aware checking: defs inside IfOp branches,
LoopOp/WhileOp/ForOp bodies are NOT visible to the enclosing scope — only
the op's result SSA index is visible.

Errors if any SSAValue is used but not defined in its scope (indicates a bug in structurization).
"""
function validate_ssa_defs(sci::StructuredIRCode)
    scope_stack = [Set{Int}()]  # stack of def sets; index 1 = outermost
    violations = Int[]
    validate_ssa_defs_scoped!(scope_stack, violations, sci.entry)
    undefined = sort!(unique!(violations))
    isempty(undefined) || error("internal error: SSA values used but not defined: ",
                                join(("%$id" for id in undefined), ", "))
    return true
end

# Check if an SSA id is defined in the current scope or any ancestor scope
function is_defined_in_scope(scope_stack::Vector{Set{Int}}, id::Int)
    for i in length(scope_stack):-1:1
        id in scope_stack[i] && return true
    end
    return false
end

# Check an SSAValue use against the scope stack, recording violations
function check_use!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, val)
    # non-SSAValue — nothing to check
end

function check_use!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, val::SSAValue)
    is_defined_in_scope(scope_stack, val.id) || push!(violations, val.id)
end

function validate_ssa_defs_scoped!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, block::Block)
    current = scope_stack[end]

    # Pre-collect all defs in this block (within a scope, order doesn't matter)
    for (idx, _) in block.body
        push!(current, idx)
    end

    # Now check uses
    for (_, entry) in block.body
        check_stmt_uses!(scope_stack, violations, entry.stmt)
    end

    check_terminator_uses!(scope_stack, violations, block.terminator)
end

# --- Statement use checking (scope-aware) ---

function check_stmt_uses!(::Vector{Set{Int}}, ::Vector{Int}, stmt)
    # Leaf types — no SSAValue references
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, val::SSAValue)
    check_use!(scope_stack, violations, val)
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, expr::Expr)
    for arg in expr.args
        arg isa SSAValue && check_use!(scope_stack, violations, arg)
    end
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, node::GotoIfNot)
    node.cond isa SSAValue && check_use!(scope_stack, violations, node.cond)
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, node::ReturnNode)
    if isdefined(node, :val) && node.val isa SSAValue
        check_use!(scope_stack, violations, node.val)
    end
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, op::IfOp)
    check_use!(scope_stack, violations, op.condition)

    # Then region: new scope
    push!(scope_stack, Set{Int}())
    validate_ssa_defs_scoped!(scope_stack, violations, op.then_region)
    pop!(scope_stack)

    # Else region: new scope (sibling, NOT shared with then)
    push!(scope_stack, Set{Int}())
    validate_ssa_defs_scoped!(scope_stack, violations, op.else_region)
    pop!(scope_stack)
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, op::LoopOp)
    for v in op.init_values
        check_use!(scope_stack, violations, v)
    end

    push!(scope_stack, Set{Int}())
    validate_ssa_defs_scoped!(scope_stack, violations, op.body)
    pop!(scope_stack)
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, op::WhileOp)
    for v in op.init_values
        check_use!(scope_stack, violations, v)
    end

    push!(scope_stack, Set{Int}())
    validate_ssa_defs_scoped!(scope_stack, violations, op.before)
    pop!(scope_stack)

    push!(scope_stack, Set{Int}())
    validate_ssa_defs_scoped!(scope_stack, violations, op.after)
    pop!(scope_stack)
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, op::ForOp)
    check_use!(scope_stack, violations, op.lower)
    check_use!(scope_stack, violations, op.upper)
    check_use!(scope_stack, violations, op.step)
    for v in op.init_values
        check_use!(scope_stack, violations, v)
    end

    push!(scope_stack, Set{Int}())
    validate_ssa_defs_scoped!(scope_stack, violations, op.body)
    pop!(scope_stack)
end

# --- Terminator use checking ---

function check_terminator_uses!(::Vector{Set{Int}}, ::Vector{Int}, term)
    # nothing terminator or unrecognized — no uses
end

function check_terminator_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, term::Union{YieldOp, ContinueOp, BreakOp})
    for v in term.values
        check_use!(scope_stack, violations, v)
    end
end

function check_terminator_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, term::ConditionOp)
    check_use!(scope_stack, violations, term.condition)
    for v in term.args
        check_use!(scope_stack, violations, v)
    end
end

check_terminator_uses!(s::Vector{Set{Int}}, v::Vector{Int}, term::ReturnNode) =
    check_stmt_uses!(s, v, term)

#=============================================================================
 SSA Uniqueness Validation
=============================================================================#

"""
    validate_ssa_uniqueness(sci::StructuredIRCode) -> Bool

Validate that no SSA index is defined in more than one block.
This should hold after `rebuildssa!` has run; any remaining duplicates
indicate a bug in the structurizer.
"""
function validate_ssa_uniqueness(sci::StructuredIRCode)
    seen = Set{Int}()
    dups = Int[]
    for block in eachblock(sci)
        for (idx, _) in block.body
            idx in seen ? push!(dups, idx) : push!(seen, idx)
        end
    end
    isempty(dups) || error("internal error: SSA indices defined in multiple blocks: ",
                           join(("%$id" for id in sort!(unique!(dups))), ", "))
    return true
end

#=============================================================================
 Type Resolution for IRValues
=============================================================================#

"""
    resolve_type(sci::StructuredIRCode, value::IRValue) -> Any

Resolve the Julia type of an IRValue.
Returns `nothing` if the type cannot be resolved.
"""
function resolve_type end

resolve_type(sci::StructuredIRCode, value::Undef) = value.type

resolve_type(sci::StructuredIRCode, value::BlockArgument) = value.type

resolve_type(sci::StructuredIRCode, value::Argument) = sci.argtypes[value.n]

resolve_type(sci::StructuredIRCode, value::SlotNumber) = sci.argtypes[value.id]

# Constants: return their runtime type
resolve_type(sci::StructuredIRCode, value) = typeof(value)

# SSAValue: search the structured IR for its definition
function resolve_type(sci::StructuredIRCode, value::SSAValue)
    for block in eachblock(sci)
        entry = get(block.body, value.id, nothing)
        entry !== nothing && return entry.typ
    end
    return nothing
end
