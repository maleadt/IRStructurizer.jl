# Structured IR validation.

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
- IfOp: both regions must have explicit terminator (never `nothing`), unless the
  region ends in an IfOp that itself diverges on both arms (`diverges`), the shape
  of a loop's exit dispatch inside a conditional continuation
- ForOp: body must have ContinueOp and no BreakOp; carries agree in arity; the IV
  type is a concrete `BitInteger`; constant bounds/step are not contradictory
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
            validate_if_terminators!(errors, sci, stmt, idx, entry.type)
        elseif stmt isa ForOp
            validate_for_terminators!(errors, sci, stmt, idx)
        elseif stmt isa WhileOp
            validate_while_terminators!(errors, sci, stmt, idx)
        elseif stmt isa LoopOp
            validate_loop_terminators!(errors, sci, stmt, idx)
        end
    end
end

# Extract the per-position expected types from an IfOp's declared result type.
# The structurizer emits `Tuple{phi_types...}` (or `Tuple{}` / `Nothing` when
# there are no yielded values). Returns `nothing` when no per-position bound is
# available, in which case per-position type checking is skipped.
function ifop_expected_yield_types(@nospecialize(result_type))
    result_type isa DataType || return nothing
    result_type <: Tuple || return nothing
    # Reject the unparameterized `Tuple` (no per-position info) and vararg
    # tuples (arity isn't fixed). Concrete abstract-element tuples like
    # `Tuple{Real}` are fine: their parameters are positionally indexable.
    result_type === Tuple && return nothing
    Base.isvatuple(result_type) && return nothing
    return result_type.parameters
end

function validate_if_terminators!(errors::Vector{String}, sci::StructuredIRCode,
                                   op::IfOp, idx::Int, @nospecialize(result_type))
    then_term = op.then_region.terminator
    else_term = op.else_region.terminator

    # Both regions must have an explicit terminator; `nothing` is valid only when
    # control cannot reach the end of the region (it ends in a diverging IfOp).
    # Valid terminators: YieldOp, ReturnNode, ContinueOp, BreakOp (for IfOps inside loops).
    if then_term === nothing && !diverges(op.then_region)
        push!(errors, "IfOp at %$idx: then region must have explicit terminator, got nothing")
    end
    if else_term === nothing && !diverges(op.else_region)
        push!(errors, "IfOp at %$idx: else region must have explicit terminator, got nothing")
    end

    # Validate yield arity and types against the IfOp's declared result type.
    #
    # Julia's own IR verifier (Compiler/src/ssair/verify.jl) only requires that
    # each phi edge value's type be a sublattice element of the phi's declared
    # type; it never compares edge values to each other. Branches may yield
    # values whose types are disjoint (e.g. `Int` and `String` joining to
    # `Union{Int,String}`, or `Int` and `Float64` joining to `Real`); what
    # matters is that each yield conforms to the declared join.
    #
    # The structurizer records that join at the IfOp's SSA entry as
    # `Tuple{phi_types...}` (see `emit_ifop_result!`), so we mirror Julia's
    # check here: for each position i, both yields must be <: the i-th element
    # of the declared tuple. `<:` is a conservative approximation of the lattice
    # `⊑` Julia uses internally; it rejects no IR that `⊑` would accept.
    if then_term isa YieldOp && else_term isa YieldOp
        then_arity = length(then_term.values)
        else_arity = length(else_term.values)
        if then_arity != else_arity
            push!(errors, "IfOp at %$idx: yield arity mismatch (then yields $then_arity, else yields $else_arity)")
        end

        expected = ifop_expected_yield_types(result_type)
        if expected !== nothing
            arity = min(then_arity, else_arity)
            # Flag yield arity that does not match the declared result tuple.
            if then_arity == else_arity && then_arity != length(expected)
                push!(errors, "IfOp at %$idx: yield arity ($then_arity) does not match declared result type $result_type (expected $(length(expected)))")
            end
            for i in 1:min(arity, length(expected))
                Ti = expected[i]
                check_yield_type!(errors, op.then_region, then_term.values[i], Ti, idx, i, "then")
                check_yield_type!(errors, op.else_region, else_term.values[i], Ti, idx, i, "else")
            end
        end
    end

    validate_terminators!(errors, sci, op.then_region)
    validate_terminators!(errors, sci, op.else_region)
end

# Check a single yield value against the IfOp's declared per-position type.
# `Undef` placeholders (used for uninitialized slots on one branch) are skipped:
# their recorded type is already the declared slot type, so the <: check is
# trivially satisfied. `block` is the yielding region, so `value_type` walks the
# parent chain and resolves SSAs defined in the surrounding scope.
function check_yield_type!(errors::Vector{String}, block::Block,
                            @nospecialize(value), @nospecialize(expected),
                            idx::Int, pos::Int, branch::String)
    value isa Undef && return
    ty = value_type(block, value)
    ty === nothing && return
    if !(ty <: expected)
        push!(errors, "IfOp at %$idx: $branch yield at position $pos has type $ty, not <: declared $expected")
    end
end

"""Whether control cannot reach the end of `block`: its last statement is an
`IfOp` none of whose arms yields, each ending in a return, continue or break, or
diverging itself. Such a block needs no terminator (a loop body ending in its
exit dispatch, or a conditional continuation of an expanded `ForOp`)."""
function diverges(block::Block)
    isempty(block.body) && return false
    last = block.body.stmts[end]
    last isa IfOp || return false
    return arm_diverges(last.then_region) && arm_diverges(last.else_region)
end

function arm_diverges(block::Block)
    term = block.terminator
    (term isa ReturnNode || term isa ContinueOp || term isa BreakOp) && return true
    return term === nothing && diverges(block)
end

function validate_for_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::ForOp, idx::Int)
    term = op.body.terminator
    if !(term isa ContinueOp)
        push!(errors, "ForOp at %$idx: body must have ContinueOp, got $(typeof(term))")
    end

    # Structural part of the counted-range contract (see the ForOp docstring).
    T = forop_iv_type(op.iv_arg.type)
    if T === nothing
        push!(errors, "ForOp at %$idx: induction variable type $(op.iv_arg.type) is not a concrete BitInteger")
    end
    n_init = length(op.init_values)
    n_args = length(op.body.args)
    if n_init != n_args
        push!(errors, "ForOp at %$idx: init_values length ($n_init) != body.args length ($n_args)")
    end
    for t in reachable_terminators(op.body)
        if t isa ContinueOp
            nc = length(t.values)
            nc == n_init || push!(errors, "ForOp at %$idx: ContinueOp has $nc values, expected $n_init (loop-carry length)")
        elseif t isa BreakOp
            push!(errors, "ForOp at %$idx: BreakOp in a counted loop body (a loop with a secondary exit must stay a LoopOp)")
        end
    end
    # Statically contradictory constants: a non-positive or mistyped literal step,
    # or an inclusive constant range whose end is off the step grid.
    if T !== nothing
        st, lo, up = op.step, op.lower, op.upper
        if st isa Integer && !(st isa T && st > zero(T))
            push!(errors, "ForOp at %$idx: step $st is not a positive $T")
        elseif op.inclusive && st isa T && lo isa T && up isa T && lo <= up &&
               (big(up) - big(lo)) % big(st) != 0
            push!(errors, "ForOp at %$idx: inclusive bound $up is not on the grid of $lo:$st")
        end
    end

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

    validate_terminators!(errors, sci, op.before)
    validate_terminators!(errors, sci, op.after)
end

function validate_loop_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::LoopOp, idx::Int)
    n_init = length(op.init_values)
    n_args = length(op.body.args)

    if n_init != n_args
        push!(errors, "LoopOp at %$idx: init_values length ($n_init) != body.args length ($n_args)")
    end

    # Every reachable ContinueOp and BreakOp must match the loop-carry length.
    for term in reachable_terminators(op.body)
        if term isa ContinueOp
            nc = length(term.values)
            nc == n_init || push!(errors, "LoopOp at %$idx: ContinueOp has $nc values, expected $n_init (loop-carry length)")
        elseif term isa BreakOp
            nb = length(term.values)
            nb == n_init || push!(errors, "LoopOp at %$idx: BreakOp has $nb values, expected $n_init (loop-carry length)")
        end
    end

    validate_terminators!(errors, sci, op.body)
end

#=============================================================================
 SSA Definition Validation
=============================================================================#

"""
    validate_ssa_defs(sci::StructuredIRCode) -> Bool

Validate that all SSAValue references in the structured IR have definitions
visible in their scope. Uses scope-aware checking: defs inside IfOp branches,
LoopOp/WhileOp/ForOp bodies are NOT visible to the enclosing scope; only
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

# Check an SSAValue use against the scope stack, recording violations.
function check_use!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, val)
    # non-SSAValue: nothing to check
end

function check_use!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, val::SSAValue)
    is_defined_in_scope(scope_stack, val.id) || push!(violations, val.id)
end

function validate_ssa_defs_scoped!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, block::Block)
    current = scope_stack[end]

    # Collect all defs in this block (within a scope, order doesn't matter).
    for (idx, _) in block.body
        push!(current, idx)
    end

    for (_, entry) in block.body
        check_stmt_uses!(scope_stack, violations, entry.stmt)
    end

    check_terminator_uses!(scope_stack, violations, block.terminator)
end

# --- Statement use checking (scope-aware) ---

function check_stmt_uses!(::Vector{Set{Int}}, ::Vector{Int}, stmt)
    # Leaf types: no SSAValue references.
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

    # Then region: new scope.
    push!(scope_stack, Set{Int}())
    validate_ssa_defs_scoped!(scope_stack, violations, op.then_region)
    pop!(scope_stack)

    # Else region: new scope, sibling, NOT shared with then.
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
    # nothing terminator or unrecognized: no uses.
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
Holds by construction, since the structurizer allocates fresh indices for inner
defs. Any duplicates indicate a bug in the structurizer.
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

