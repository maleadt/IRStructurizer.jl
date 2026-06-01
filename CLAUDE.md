# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

IRStructurizer is a Julia package that converts unstructured Julia SSA IR into structured control flow representation (SCF-style operations). It's part of the cuTile.jl GPU kernel compilation pipeline:

```
Julia function → Julia SSA IR → Structured IR (IRStructurizer) → Tile IR bytecode → CUBIN
```

## Running Tests

```bash
julia --project -e 'using Pkg; Pkg.test()'
```

## Public API

```julia
using IRStructurizer

# High-level: get structured IR for a function
sci, ret_type = code_structured(f, Tuple{ArgTypes...})

# Low-level: from IRCode directly
ir, _ = only(code_ircode(f, argtypes))
sci = StructuredIRCode(ir)                              # structurize + validate
sci = StructuredIRCode(ir; structurize=false)           # flat view (for testing)
sci = StructuredIRCode(ir; validate=false)              # skip validation
```

The `code_structured` function uses `Base.code_ircode()` internally and returns structured IR with nested control flow operations (IfOp, ForOp, WhileOp, LoopOp).

## Architecture

### Core Data Structures (`src/ir.jl`)

**Control Flow Operations** (all subtypes of `ControlFlowOp`):
- `IfOp`: Structured if-then-else with condition, then_region, else_region
- `ForOp`: Counted for-loop with lower/upper/step bounds and induction variable
- `WhileOp`: Condition-at-header loop with before (condition) and after (body) regions
- `LoopOp`: General loop with dynamic exit via BreakOp/ContinueOp

**Terminator Operations**:
- `YieldOp`: Yields values from if/loop branches
- `ContinueOp`: Continue to next loop iteration with updated values
- `BreakOp`: Exit loop with results
- `ConditionOp`: Terminator for WhileOp's before region

**Block Structure**:
```julia
mutable struct Block
    args::Vector{BlockArg}      # Loop-carried values (like MLIR block arguments)
    body::SSAVector             # (ssa_idx, stmt, type) triples
    terminator::Terminator
end
```

### Structurization Pipeline

Uses Julia's `IRCode` infrastructure (from `code_ircode`):

- **`src/cfg.jl`**: Backedge detection and edge classification using `Core.Compiler.construct_domtree()`
- **`src/control_tree.jl`**: Pattern matching to build control tree (ControlTree), accesses `ir.cfg.blocks` directly
- **`src/structure.jl`**: Converts control tree to structured IR (IfOp, ForOp, etc.)

Key functions:
- `backedges()`: Identifies loop back-edges using Julia's DomTree
- `ControlTree()`: Builds hierarchical control tree via pattern matching
- `try_detect_for_loop()`: Recognizes counted for-loops from phi/condition patterns
- `handle_proper_region!()`: Lowers multi-exit acyclic regions (short-circuit `||`/`&&`) to nested IfOps

### Validation (`src/validation.jl`)

`validate_scf(sci)` ensures all GotoNode/GotoIfNot have been replaced with structured operations. Throws `UnstructuredControlFlowError` if unstructured control flow remains.

## Key Design Decisions

1. **Uses Julia's IRCode**: Leverages pre-computed CFG and dominator infrastructure from `Core.Compiler`
2. **Explicit block arguments**: Loop-carried values are explicit (like MLIR), not implicit through SSA
3. **For-loop recognition**: Automatically detects counted loops and uses `ForOp`
4. **Minimal storage**: `StructuredIRCode` stores only `stmts` and `types` vectors, not the full `IRCode`

## Pretty Printing

The output uses MLIR SCF-style syntax:
```
StructuredIRCode {
  %1 = Base.slt_int(0, x) : Bool
  scf.if %1 {
    %3 = Base.add_int(x, 1) : Int64
    scf.yield %3
  } else {
    %5 = Base.sub_int(x, 1) : Int64
    scf.yield %5
  }
  return %3
}
```
