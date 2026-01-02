module IRStructurizer

using Core: MethodInstance, CodeInfo, SSAValue, Argument, SlotNumber,
            GotoNode, GotoIfNot, ReturnNode, PhiNode, PiNode, QuoteNode, GlobalRef

# data structures
include("graph.jl")           # DeltaGraph, SimpleTree, tree utilities

# CFG analysis
include("dominance.jl")       # dominators, edge classification, DFS

# block extraction
include("blocks.jl")          # BlockInfo, find_basic_blocks, build_block_cfg

# control tree construction
include("control_tree.jl")    # RegionType, patterns, ControlTree, ForLoopInfo

# structured IR definitions
include("ir.jl")
include("show.jl")

# control tree to structured IR
include("structure.jl")

# validation and public API
include("validation.jl")
include("interface.jl")

end
