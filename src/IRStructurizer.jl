module IRStructurizer

using Core: MethodInstance, CodeInfo, SSAValue, Argument, SlotNumber,
            GotoNode, GotoIfNot, ReturnNode, PhiNode, PiNode, QuoteNode, GlobalRef

using Core.Compiler: IRCode, CFG, BasicBlock, InstructionStream, StmtRange,
                     construct_domtree, DomTree, dominates, bb_unreachable,
                     widenconst
using Base: code_ircode

# auxiliary data structures and analyses
include("graph.jl")
include("cfg.jl")

# control tree construction
include("control_tree.jl")

# structured IR definitions
include("ir/types.jl")
include("ir/show.jl")

# control tree to structured IR
include("structurize/substitutions.jl")
include("structurize/helpers.jl")
include("structurize/regions.jl")
include("structurize/loops.jl")

# IR utilities & validation
include("ir/utilities.jl")
include("ir/validation.jl")

# unstructurize: StructuredIRCode → IRCode
include("unstructurize.jl")

# public API
include("interface.jl")
include("precompile.jl")

end
