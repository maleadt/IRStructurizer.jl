using Test
using FileCheck
using InteractiveUtils: code_llvm

using IRStructurizer
using Core: SSAValue, ReturnNode, GotoNode, GotoIfNot, PhiNode, PiNode

# Internal types used in tests for type-checking structured IR output
using IRStructurizer: Block, ControlFlowOp, IfOp, ForOp, WhileOp, LoopOp,
                      YieldOp, ContinueOp, BreakOp, ConditionOp,
                      validate_scf, validate_terminators, validate_ssa_defs,
                      statements, BlockArgument, SourceLocation
using Base: code_ircode

# Used by "step defined inside loop body" test — must be module-level const
const _STEP_REF = Ref(2)

#=============================================================================
 Roundtrip test helpers
=============================================================================#

"""
    execute(sci::StructuredIRCode, args...)

Convert a StructuredIRCode to IRCode and execute it via OpaqueClosure.
"""
function execute(sci::StructuredIRCode, args...)
    CC = Core.Compiler
    ir = CC.copy(CC.IRCode(sci))
    ir.argtypes[1] = Tuple{}
    @static if VERSION >= v"1.12-"
        ir.debuginfo.def = Symbol("unstructurized")
    end
    oc = Core.OpaqueClosure(ir)
    return oc(args...)
end

"""
    @roundtrip f(args...)

Structurize then unstructurize a function call and compare the result to direct
execution. Returns `true` if results match. Use as `@test @roundtrip f(1, 2)`.
"""
macro roundtrip(call_expr)
    Meta.isexpr(call_expr, :call) ||
        error("@roundtrip expects a function call, got: $call_expr")
    f = call_expr.args[1]
    args = call_expr.args[2:end]
    quote
        let f = $(esc(f)), args = ($(map(esc, args)...),)
            expected = f(args...)
            argtypes = Tuple{map(typeof, args)...}
            sci, _ = code_structured(f, argtypes) |> only
            result = execute(sci, args...)
            result == expected
        end
    end
end

@testset "IRStructurizer" verbose=true begin
    include("interface.jl")
    include("structurize.jl")
    include("multiplex.jl")
    include("ir.jl")
    include("unstructurize.jl")
    include("debuginfo.jl")
end
