# public API

export code_structured, structurize!, StructuredIRCode

"""
    code_structured(f, argtypes; validate=true, kwargs...) -> Pair{StructuredIRCode, DataType}

Get the structured IR for a function with the given argument types.

This is analogous to `code_typed` but returns a `StructuredIRCode` with
control flow restructured into nested SCF-style operations (if/for/while).

# Arguments
- `f`: The function to analyze
- `argtypes`: Argument types as a tuple of types (e.g., `(Int, Float64)`)
- `validate`: Whether to validate that all control flow was properly structured (default: true).
  When `true`, throws `UnstructuredControlFlowError` if any unstructured control flow remains.

Other keyword arguments are passed to `code_ircode`.

ForOp is created directly during CFG analysis for loops that match counting patterns
(while i < n with i += step, or for i in 1:n). WhileOp is used for condition-at-header
loops that don't match counting patterns. LoopOp is used for general cyclic regions.

# Returns
A `Pair{StructuredIRCode, DataType}` where the first element is the structured IR
and the second is the return type. Displays with MLIR SCF-style syntax.

# Example
```julia
julia> f(x) = x > 0 ? x + 1 : x - 1

julia> code_structured(f, Tuple{Int})
StructuredIRCode(
│ %1 = Base.slt_int(0, x)::Bool
│ ...
└ return %3
) => Int64

julia> sci, ret_type = code_structured(f, Tuple{Int})  # destructure
```
"""
function code_structured(@nospecialize(f), @nospecialize(argtypes);
                         validate::Bool=true, kwargs...)
    ir, ret_type = only(code_ircode(f, argtypes; kwargs...))
    sci = StructuredIRCode(ir)
    structurize!(sci; validate)
    return sci => ret_type
end

"""
    structurize!(sci::StructuredIRCode; validate=true) -> StructuredIRCode

Convert unstructured control flow in `sci` to structured control flow operations
(IfOp, ForOp, WhileOp, LoopOp) in-place.

This transforms GotoNode and GotoIfNot statements into nested structured ops
that can be traversed hierarchically.

ForOp is created directly during CFG analysis for loops matching counting patterns.
WhileOp is used for condition-at-header loops. LoopOp is used for general cyclic regions.

Returns `sci` for convenience (allows chaining).
"""
function structurize!(sci::StructuredIRCode; validate::Bool=true)
    ircode = ir(sci)  # Get the underlying IRCode
    types = ircode.stmts.type

    n = length(ircode.stmts.stmt)
    n == 0 && return sci
    ctx = StructurizationContext(types, n + 1)

    # Build control tree directly from IRCode
    ctree = ControlTree(ircode)

    # Build structured IR
    entry = control_tree_to_structured_ir(ctree, ircode, ctx)
    validate && validate_scf(entry)
    validate && validate_no_phis(entry)
    sci.entry = entry
    sci.max_ssa_idx = ctx.next_ssa_idx - 1  # Update to include synthesized indices

    return sci
end
