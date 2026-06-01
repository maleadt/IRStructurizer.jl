# TODO: Handle irreducible control flow

## The problem

RESEARCH.md claims Julia's IRCode is always reducible. This is false.
`@goto` can create irreducible CFGs:

```julia
function irreducible(x::Int, y::Int)
    if x > 0; @goto L2; end
    @label L1; y += x
    if y > 100; return y; end
    @goto L2_body
    @label L2; @label L2_body; y += 1
    if y > 100; return y; end
    @goto L1
end
```

This produces an SCC {BB3, BB6} with two entries from BB1 — neither dominates
the other. Julia's own compiler handles this (`Compiler/src/ssair/tarjan.jl`
has `CFGReachability` with an explicit `irreducible::BitVector`).

The structurizer currently **hangs** on irreducible input: `compute_natural_loops`
finds zero backedges (no header dominates a latch), so no loop is detected, and
`structurize_region!` walks the cycle forever.

## Immediate fix: detect and reject

Add SCC detection in `structurize()`. If any non-trivial SCC has multiple entry
blocks, throw `UnstructuredControlFlowError`. ~20 lines. The `using Graphs`
import in `structurize.jl` is already present and unused — intended for this.

## Full fix: entry multiplexer (MLIR's approach)

MLIR's CFGToSCF handles multi-entry SCCs by inserting an **entry multiplexer**:
a synthetic dispatch block that becomes the single entry point. After
multiplexing, the SCC is a natural loop and the existing algorithm handles it.

### Algorithm

1. **SCC detection**: Replace `compute_natural_loops` with SCC-based cycle
   detection via `strongly_connected_components` from Graphs.jl. Single-entry
   SCCs are natural loops (handled as today). Multi-entry SCCs need multiplexing.

2. **Entry multiplexer**: For a multi-entry SCC with entries {E0, E1, ...}:
   - Add a **discriminator** as an extra loop-carried value
   - The loop body starts with a dispatch IfOp chain:
     `if disc == 0 { E0_body } else { E1_body }`
   - ALL edges into the SCC (external entries + internal back edges) route
     through the dispatch by setting the discriminator
   - Phi values from all entry blocks form a **union**; each entry passes its
     values at the correct positions and `Undef` for other entries' slots

3. **Back edge routing**: When a back edge inside the SCC targets entry Ek,
   `ContinueOp` carries `(disc=k, values_for_Ek..., Undef_for_others...)`.

### What changes

| Component | ~Lines | Modifies existing code? |
|-----------|--------|------------------------|
| SCC detection + entry classification | 40 | Replaces `compute_natural_loops` |
| `StructurizeCtx.multi_entry` field | 10 | Extends struct |
| `emit_irreducible_loop!` with dispatch IfOp | 100-120 | New function |
| Entry phi union + Undef filling | 40-50 | New code |
| `resolve_dest` discriminator-aware ContinueOp | 20 | Minor extension |
| Tests | 50-80 | New tests |
| **Total** | **~280-320** | |

### What stays the same

Everything else: `structurize_region!`, `emit_branch!`, `find_branch_regions`,
`LoopCtx`, `promote_loops!`, `apply_substitutions!`, `rebuildssa!`, validation,
show, unstructurize. Irreducible loops stay as `LoopOp` (no WhileOp/ForOp
promotion since there's no single condition).

### References

- MLIR CFGToSCF: `mlir/lib/Transforms/Utils/CFGToSCF.cpp` — `EdgeMultiplexer`
  class (lines 214-389), `transformCyclesToSCFLoops` (lines 803-896)
- Bahmann et al. 2015, "Perfect Reconstructability of Control Flow from Demand
  Dependence Graphs"
- Julia's `Compiler/src/ssair/tarjan.jl` — `CFGReachability`, `bb_in_irreducible_loop`
