module IRStructurizer

using Core: MethodInstance, CodeInfo, SSAValue, Argument, SlotNumber,
            GotoNode, GotoIfNot, ReturnNode, PhiNode, PiNode, QuoteNode, GlobalRef

using Core.Compiler: IRCode, CFG, BasicBlock, InstructionStream, StmtRange,
                     construct_domtree, DomTree, dominates,
                     CFGReachability,
                     widenconst,
                     WorldRange
using Base: code_ircode

# structured IR definitions
include("ir/types.jl")
include("ir/show.jl")

# explicit-edge mutable CFG types (MBlock/MCFG). Defined before the lift so that
# StructurizeCtx and its method signatures can name them; operations live in multiplex.jl.
include("structurize/mcfg.jl")

# substitution machinery (phi refs to block args)
include("structurize/substitutions.jl")

# structurization: IRCode to StructuredIRCode
include("structurize.jl")
include("structurize/promote.jl")

# IR utilities & validation
include("ir/utilities.jl")
include("ir/validation.jl")

# unstructurize: StructuredIRCode to IRCode
include("unstructurize.jl")

# mutate-then-lift CFG normalization (EdgeMultiplexer)
include("structurize/multiplex.jl")

# public API
include("interface.jl")
include("precompile.jl")

end
