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
- IfOp: both regions must have explicit terminator (never `nothing`)
- ForOp body: must have ContinueOp
- WhileOp before: must have ConditionOp
- WhileOp after: must have YieldOp
- LoopOp body: recursively validate nested ops
- TryOp: body and handler must have explicit terminators; a LeaveOp may only sit
  inside a TryOp body (through IfOps and inner handlers), never across a loop, and
  no BreakOp or ContinueOp may exit a body or handler;
  the body and handler yields and the LeaveOps that exit the body carry the op's
  results (arity and types); no value return inside the body; the body has no
  arguments, and the handler one per upsilon list (none without a handler); every
  listed upsilon is an UpsilonNode in the body or before the op and feeds a single
  handler argument
"""
function validate_terminators(sci::StructuredIRCode)
    errors = String[]
    walk = TerminatorWalk()
    validate_terminators!(errors, sci, sci.entry, walk)
    if !isempty(walk.tries)
        validate_try_upsilons!(errors, sci, walk.tries)
        validate_try_refs!(errors, sci, walk.tries)
    end
    isempty(errors) || error("internal error: invalid terminators: ",
                              join(errors, "; "))
    return true
end

# What the terminator walk carries down: whether the current block sits in a try
# body, where a LeaveOp may end it (through IfOp arms and inner try handlers; loops
# and inner try bodies are boundaries); whether it sits in a try body or handler
# since the innermost loop, where a BreakOp or ContinueOp may not end it; and the
# TryOps seen so far, whose upsilons are checked afterwards. Code without a TryOp
# pays no extra walk.
mutable struct TerminatorWalk
    in_try::Bool
    in_try_region::Bool
    tries::Vector{Pair{Int, TryOp}}
end
TerminatorWalk() = TerminatorWalk(false, false, Pair{Int, TryOp}[])

# Walk `b` with the flags set as given, restoring them afterwards.
function validate_region_terminators!(errors::Vector{String}, sci::StructuredIRCode,
                                      b::Block, walk::TerminatorWalk, in_try::Bool,
                                      in_try_region::Bool=in_try)
    saved = (walk.in_try, walk.in_try_region)
    walk.in_try, walk.in_try_region = in_try, in_try_region
    validate_terminators!(errors, sci, b, walk)
    walk.in_try, walk.in_try_region = saved
end

# Convenience method for testing: wrap block in minimal SCI
function validate_terminators(entry::Block)
    sci = StructuredIRCode(Any[], Any[], entry, 0)
    return validate_terminators(sci)
end

function validate_terminators!(errors::Vector{String}, sci::StructuredIRCode, block::Block,
                               walk::TerminatorWalk=TerminatorWalk())
    block.terminator isa LeaveOp && !walk.in_try &&
        push!(errors, "LeaveOp outside a TryOp body")
    # A loop exit from a try body would skip leaving it, and the lift routes every
    # exit of a try, from its handler too, through the op's continuation.
    block.terminator isa Union{BreakOp, ContinueOp} && walk.in_try_region &&
        push!(errors, "$(nameof(typeof(block.terminator))) out of a TryOp")
    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa IfOp
            validate_if_terminators!(errors, sci, stmt, idx, entry.type, walk)
        elseif stmt isa ForOp
            validate_for_terminators!(errors, sci, stmt, idx, walk)
        elseif stmt isa WhileOp
            validate_while_terminators!(errors, sci, stmt, idx, walk)
        elseif stmt isa LoopOp
            validate_loop_terminators!(errors, sci, stmt, idx, walk)
        elseif stmt isa TryOp
            push!(walk.tries, idx => stmt)
            validate_try_terminators!(errors, sci, stmt, idx, entry.type, walk)
        end
        stmt isa LoopOps && check_carry_types!(errors, block, stmt, idx, entry.type)
    end
end

function validate_try_terminators!(errors::Vector{String}, sci::StructuredIRCode,
                                   op::TryOp, idx::Int, @nospecialize(result_type),
                                   walk::TerminatorWalk=TerminatorWalk())
    for (name, b) in (("body", op.body), ("handler", op.handler))
        b === nothing && continue
        b.terminator === nothing &&
            push!(errors, "TryOp at %$idx: $name must have explicit terminator, got nothing")
        b.terminator isa ConditionOp &&
            push!(errors, "TryOp at %$idx: $name cannot end in ConditionOp")
        # A LeaveOp exits the innermost try body; the handler runs with this try's
        # handler popped, so it answers to the enclosing body.
        validate_region_terminators!(errors, sci, b, walk, b === op.body || walk.in_try, true)
    end
    isempty(op.body.args) ||
        push!(errors, "TryOp at %$idx: body has $(length(op.body.args)) arguments")
    nargs = op.handler === nothing ? 0 : length(op.handler.args)
    length(op.upsilons) == nargs ||
        push!(errors, "TryOp at %$idx: $(length(op.upsilons)) upsilon lists for $nargs handler arguments")

    # Every exit to the continuation carries the op's results: the yields that end
    # the body and the handler, and the LeaveOps that exit this body.
    expected = result_type === Nothing ? () : ifop_expected_yield_types(result_type)
    if expected !== nothing
        exits = Pair{String, Block}[]
        op.body.terminator isa YieldOp && push!(exits, "body yield" => op.body)
        op.handler !== nothing && op.handler.terminator isa YieldOp &&
            push!(exits, "handler yield" => op.handler)
        collect_try_leaves!(exits, op.body)
        for (what, b) in exits
            vals = (b.terminator::Union{YieldOp, LeaveOp}).values
            if length(vals) != length(expected)
                push!(errors, "TryOp at %$idx: $what carries $(length(vals)) values for result type $result_type")
                continue
            end
            check_operand_types!(errors, b, vals, expected, "TryOp at %$idx: $what")
        end
    end

    # A value return would leave the body without popping its handler (or scope):
    # exits from a try go through its continuation.
    has_value_return(op.body) &&
        push!(errors, "TryOp at %$idx: a value return inside the body (exits must leave through the continuation)")
end

# The blocks ending in a LeaveOp that exits `block`'s try body: through IfOp arms and
# inner TryOp handlers, which run inside this body; loops and inner try bodies are
# boundaries (as in `TerminatorWalk`).
function collect_try_leaves!(out::Vector{Pair{String, Block}}, block::Block)
    block.terminator isa LeaveOp && push!(out, "leave" => block)
    for (_, entry) in block.body
        stmt = entry.stmt
        if stmt isa IfOp
            foreach(b -> collect_try_leaves!(out, b), blocks(stmt))
        elseif stmt isa TryOp && stmt.handler !== nothing
            collect_try_leaves!(out, stmt.handler)
        end
    end
    return out
end

function has_value_return(block::Block)
    t = block.terminator
    t isa ReturnNode && isdefined(t, :val) && return true
    for (_, entry) in block.body
        entry.stmt isa ControlFlowOp || continue
        any(has_value_return, blocks(entry.stmt)) && return true
    end
    return false
end

# Each listed upsilon of a TryOp handler argument names an UpsilonNode statement that
# can run before the handler and feeds no other argument (Julia maps each upsilon to
# one PhiCNode). Its value is not checked against the argument's type, which Julia's
# IR does not guarantee either: a `Union{}` PhiCNode can have an `Int` upsilon.
function validate_try_upsilons!(errors::Vector{String}, sci::StructuredIRCode,
                                tries::Vector{Pair{Int, TryOp}})
    wanted = Set{Int}(first(t) for t in tries)
    for (_, op) in tries, us in op.upsilons
        union!(wanted, us)
    end
    paths = Dict{Int, Vector{Tuple{Block, Int}}}()
    upsilons = Set{Int}()
    stmt_paths!(paths, upsilons, wanted, sci.entry, Tuple{Block, Int}[])
    fed = Dict{Int, Tuple{Int, Int}}()
    for (idx, op) in tries, (k, us) in enumerate(op.upsilons), u in us
        what = "TryOp at %$idx: upsilon %$u of handler argument $k"
        if !(u in upsilons)
            push!(errors, "$what is not an UpsilonNode")
            continue
        elseif !runs_before_handler(paths[u], paths[idx], op)
            push!(errors, "$what is neither in the body nor before the op")
        end
        get!(fed, u, (idx, k)) == (idx, k) ||
            push!(errors, "$what also feeds another handler argument")
    end
end

# `%t` names a TryOp's results, read with `getfield(%t, i)` after the op, and, as the
# operand of `pop_exception`, the try's enter. `IRCode(sci)` maps every other use to
# the enter, so no other use may exist.
function validate_try_refs!(errors::Vector{String}, sci::StructuredIRCode,
                            tries::Vector{Pair{Int, TryOp}})
    refs = Dict{Int, Int}(idx => 0 for (idx, _) in tries)
    count_try_refs!(errors, refs, sci.entry, Int[])
    index = uses(sci.entry)
    for (idx, _) in tries
        length(index[SSAValue(idx)]) == refs[idx] ||
            push!(errors, "TryOp at %$idx: %$idx used other than by getfield or pop_exception")
    end
end

# Count the `getfield` and `pop_exception` references to each TryOp, rejecting a
# `getfield` inside the op it reads (`inside`: the enclosing TryOps).
function count_try_refs!(errors::Vector{String}, refs::Dict{Int, Int}, block::Block,
                         inside::Vector{Int})
    for (idx, entry) in block.body
        stmt = entry.stmt
        if stmt isa Expr && length(stmt.args) == 1 && stmt.head === :pop_exception
            t = stmt.args[1]
            t isa SSAValue && haskey(refs, t.id) && (refs[t.id] += 1)
        elseif stmt isa Expr && stmt.head === :call && length(stmt.args) == 3 &&
               stmt.args[1] === Core.getfield
            t = stmt.args[2]
            if t isa SSAValue && haskey(refs, t.id)
                refs[t.id] += 1
                t.id in inside && push!(errors, "TryOp at %$(t.id): its result is read inside it")
            end
        elseif stmt isa ControlFlowOp
            stmt isa TryOp && push!(inside, idx)
            foreach(b -> count_try_refs!(errors, refs, b, inside), blocks(stmt))
            stmt isa TryOp && pop!(inside)
        end
    end
end

# The nesting path of each statement in `wanted`: its block and position in it at
# each level, from the entry block down. Also collects which of them are upsilons.
function stmt_paths!(paths, upsilons::Set{Int}, wanted::Set{Int}, block::Block,
                     stack::Vector{Tuple{Block, Int}})
    for (pos, (idx, entry)) in enumerate(block.body)
        push!(stack, (block, pos))
        if idx in wanted
            paths[idx] = copy(stack)
            entry.stmt isa Core.UpsilonNode && push!(upsilons, idx)
        end
        if entry.stmt isa ControlFlowOp
            for b in blocks(entry.stmt)
                stmt_paths!(paths, upsilons, wanted, b, stack)
            end
        end
        pop!(stack)
    end
end

# An upsilon can feed the handler if it sits in the op's body, or anywhere before the
# op in program order (lowering resolves the list when it reaches the handler): where
# the two paths part, the upsilon's branch comes first in the same block.
function runs_before_handler(pu, pt, op::TryOp)
    n = length(pt)
    length(pu) > n && view(pu, 1:n) == pt && return first(pu[n+1]) === op.body
    for L in 1:min(length(pu), n)
        pu[L] == pt[L] && continue
        return first(pu[L]) === first(pt[L]) && last(pu[L]) < last(pt[L])
    end
    return false
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

function validate_if_terminators!(errors::Vector{String}, sci::StructuredIRCode,
                                   op::IfOp, idx::Int, @nospecialize(result_type),
                                   walk::TerminatorWalk=TerminatorWalk())
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

    # Validate yield arity and types against the IfOp's declared result type,
    # `Tuple{phi_types...}` (see `emit_ifop_result!`). Branches may yield values
    # of disjoint types (`Int` and `String` joining to `Union{Int,String}`); each
    # must conform to the declared join.
    #
    # This is stricter than Julia, whose verifier (Compiler/src/ssair/verify.jl)
    # leaves a phi operand wider than the phi unchecked: inference may type the
    # phi by a refinement that only holds on the edge. The structurizer makes
    # such a refinement explicit with a `PiNode` (see `narrow_edge_value!`).
    if then_term isa YieldOp && else_term isa YieldOp
        then_arity = length(then_term.values)
        else_arity = length(else_term.values)
        if then_arity != else_arity
            push!(errors, "IfOp at %$idx: yield arity mismatch (then yields $then_arity, else yields $else_arity)")
        end

        expected = ifop_expected_yield_types(result_type)
        if expected !== nothing
            # Flag yield arity that does not match the declared result tuple.
            if then_arity == else_arity && then_arity != length(expected)
                push!(errors, "IfOp at %$idx: yield arity ($then_arity) does not match declared result type $result_type (expected $(length(expected)))")
            end
            check_operand_types!(errors, op.then_region, then_term.values, expected,
                                 "IfOp at %$idx: then yield")
            check_operand_types!(errors, op.else_region, else_term.values, expected,
                                 "IfOp at %$idx: else yield")
        end
    end

    validate_terminators!(errors, sci, op.then_region, walk)
    validate_terminators!(errors, sci, op.else_region, walk)
end

# Check the values `block` passes on (a terminator's operands, or an op's init
# values) against the types of the arguments or results they bind. `Undef`
# placeholders are typed by their slot. `value_type` walks `block`'s parent chain,
# so SSAs defined in an enclosing scope resolve.
function check_operand_types!(errors::Vector{String}, block::Block, values, expected,
                              what::String)
    for (i, (value, T)) in enumerate(zip(values, expected))
        value isa Undef && continue
        ty = value_type(block, value)
        ty === nothing || ty <: T ||
            push!(errors, "$what at position $i has type $ty, not <: declared $T")
    end
end

# Check a loop's carried values against the region arguments and results they
# bind, from the block containing the loop and from each exit.
function check_carry_types!(errors::Vector{String}, block::Block, op::LoopOps, idx::Int,
                            @nospecialize(result_type))
    arg_types(b::Block) = Any[a.type for a in b.args]
    carry_types = arg_types(body_block(op))
    results = something(ifop_expected_yield_types(result_type), Any[])
    check_operand_types!(errors, block, op.init_values, carry_types,
                         "$(nameof(typeof(op))) at %$idx: init value")
    # A ForOp has no exit terminator: its results are its carries when it ends.
    if op isa ForOp
        for (i, (T, R)) in enumerate(zip(carry_types, results))
            T <: R || push!(errors, "ForOp at %$idx: carry at position $i has type $T, not <: declared $R")
        end
    end
    exits = op isa WhileOp ? [reachable_exits(op.before); reachable_exits(op.after)] :
                             reachable_exits(op.body)
    for (blk, term) in exits
        if term isa ConditionOp
            check_operand_types!(errors, blk, term.args, arg_types((op::WhileOp).after),
                                 "WhileOp at %$idx: condition argument")
            check_operand_types!(errors, blk, term.args, results,
                                 "WhileOp at %$idx: condition argument")
        elseif term isa BreakOp
            check_operand_types!(errors, blk, term.values, results,
                                 "$(nameof(typeof(op))) at %$idx: break value")
        else
            check_operand_types!(errors, blk, operands(term), carry_types,
                                 "$(nameof(typeof(op))) at %$idx: $(nameof(typeof(term))) value")
        end
    end
end

function validate_for_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::ForOp, idx::Int,
                                   walk::TerminatorWalk=TerminatorWalk())
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
    if T !== nothing
        for (name, operand) in ((:lower, op.lower), (:upper, op.upper), (:step, op.step))
            ty = argextype(sci, operand)
            if ty === nothing || widenconst(ty) !== T
                push!(errors, "ForOp at %$idx: $name must have induction variable type $T")
            end
        end
        constant(v) = (ty = argextype(sci, v); ty isa CC.Const ? ty.val : nothing)
        st, lo, up = constant(op.step), constant(op.lower), constant(op.upper)
        if st isa T && st <= zero(T)
            push!(errors, "ForOp at %$idx: step $st is not positive")
        elseif st isa T && lo isa T && up isa T
            if op.inclusive && lo <= up && (big(up) - big(lo)) % big(st) != 0
                push!(errors, "ForOp at %$idx: inclusive bound $up is not on the grid of $lo:$st")
            elseif !op.inclusive && lo < up
                last = big(lo) + div(big(up) - 1 - big(lo), big(st)) * big(st)
                if last + big(st) > big(typemax(T))
                    push!(errors, "ForOp at %$idx: exclusive final increment is not representable in $T")
                end
            end
        end
    end

    validate_region_terminators!(errors, sci, op.body, walk, false)
end

function validate_while_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::WhileOp, idx::Int,
                                     walk::TerminatorWalk=TerminatorWalk())
    before_term = op.before.terminator
    after_term = op.after.terminator

    if !(before_term isa ConditionOp)
        push!(errors, "WhileOp at %$idx: before region must have ConditionOp, got $(typeof(before_term))")
    end
    if !(after_term isa YieldOp)
        push!(errors, "WhileOp at %$idx: after region must have YieldOp, got $(typeof(after_term))")
    end

    validate_region_terminators!(errors, sci, op.before, walk, false)
    validate_region_terminators!(errors, sci, op.after, walk, false)
end

function validate_loop_terminators!(errors::Vector{String}, sci::StructuredIRCode, op::LoopOp, idx::Int,
                                    walk::TerminatorWalk=TerminatorWalk())
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

    validate_region_terminators!(errors, sci, op.body, walk, false)
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

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, node::Core.UpsilonNode)
    isdefined(node, :val) && check_use!(scope_stack, violations, node.val)
end

function check_stmt_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, op::TryOp)
    has_scope(op) && check_use!(scope_stack, violations, op.scope)
    for b in blocks(op)
        push!(scope_stack, Set{Int}())
        validate_ssa_defs_scoped!(scope_stack, violations, b)
        pop!(scope_stack)
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

function check_terminator_uses!(scope_stack::Vector{Set{Int}}, violations::Vector{Int}, term::Union{YieldOp, ContinueOp, BreakOp, LeaveOp})
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

