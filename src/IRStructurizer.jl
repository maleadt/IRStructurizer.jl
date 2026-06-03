module IRStructurizer

using Core: MethodInstance, CodeInfo, SSAValue, Argument, SlotNumber,
            GotoNode, GotoIfNot, ReturnNode, PhiNode, PiNode, QuoteNode, GlobalRef

using Core.Compiler: IRCode, CFG, BasicBlock, InstructionStream, StmtRange,
                     construct_domtree, DomTree, dominates,
                     CFGReachability,
                     widenconst,
                     WorldRange
using Base: code_ircode

# structured IR: data structures and pretty-printing
include("ir/types.jl")
include("ir/show.jl")

# structured IR: mutation, use tracking, loop carries, traversal, inspection
include("ir/blocks.jl")
include("ir/uses.jl")
include("ir/carries.jl")
include("ir/traversal.jl")
include("ir/inspect.jl")
include("ir/validation.jl")

# explicit-edge mutable CFG (MBlock/MCFG) and the phi-to-block-arg substitutions,
# both named by the structurize pipeline below
include("structurize/mcfg.jl")
include("structurize/substitutions.jl")

# structurize: IRCode -> StructuredIRCode, as ingest -> normalize -> lift -> promote
include("structurize/ingest.jl")
include("structurize/multiplex.jl")
include("structurize/normalize.jl")
include("structurize.jl")
include("structurize/promote.jl")

# unstructurize: StructuredIRCode -> IRCode (test-only reverse)
include("unstructurize.jl")

# public API
include("interface.jl")
include("precompile.jl")

end
