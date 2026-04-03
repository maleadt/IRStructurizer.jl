module IRStructurizer

using Core: MethodInstance, CodeInfo, SSAValue, Argument, SlotNumber,
            GotoNode, GotoIfNot, ReturnNode, PhiNode, PiNode, QuoteNode, GlobalRef

using Core.Compiler: IRCode, CFG, BasicBlock, InstructionStream, StmtRange,
                     construct_domtree, DomTree, dominates, bb_unreachable,
                     widenconst
using Base: code_ircode

# structured IR definitions
include("ir/types.jl")
include("ir/show.jl")

# substitution machinery (phi refs → block args)
include("structurize/substitutions.jl")

# structurization: IRCode → StructuredIRCode
include("structurize.jl")
include("structurize/promote.jl")

# IR utilities & validation
include("ir/utilities.jl")
include("ir/validation.jl")

# unstructurize: StructuredIRCode → IRCode
include("unstructurize.jl")

# public API
include("interface.jl")
include("precompile.jl")

end
