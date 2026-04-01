using Test
using FileCheck

using IRStructurizer
using Core: SSAValue, ReturnNode, GotoNode, GotoIfNot, PhiNode

# Internal types used in tests for type-checking structured IR output
using IRStructurizer: Block, ControlFlowOp, IfOp, ForOp, WhileOp, LoopOp,
                      YieldOp, ContinueOp, BreakOp, ConditionOp,
                      validate_scf, validate_terminators, validate_ssa_defs,
                      statements, BlockArgument
using Base: code_ircode

# Used by "step defined inside loop body" test — must be module-level const
const _STEP_REF = Ref(2)

@testset "IRStructurizer" verbose=true begin
    include("interface.jl")
    include("structurize.jl")
    include("ir.jl")
end
