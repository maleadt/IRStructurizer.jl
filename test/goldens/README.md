# MLIR golden references for the divergence CFGs

Reference captures of MLIR's `CFGToSCF` output for the three divergence CFGs
from `RESEARCH_ANSWER.md` (Q1/Q2/Q3). They document that MLIR's principled
algorithm produces the structure our structurizer is held to.

**These are reference artifacts, not a CI build dependency.** The executable
assertions live in `test/corpus.jl` (merge selection, body-emitted-once,
renumbering invariance + roundtrip). These `.mlir` files let a reviewer confirm,
by eye, that those assertions match upstream MLIR.

Regenerate with LLVM ≥ 22 (research cited 23.0.0git; the predicates are stable):

```
mlir-opt --lift-cf-to-scf qN.cf.mlir
```

## Correspondence to our output

| CFG | MLIR `scf` shape | Our shape | Shared invariant |
|-----|------------------|-----------|------------------|
| **Q1** | one `scf.if %c { yield 10 } else { yield 20 }` | `IfOp` with empty then-arm, `F` in else, continuation `T` | merge = `T` (edge-domination, not block-domination); I3 |
| **Q2** | if-tree yields `(M_val, R_val, disc)`, then `scf.index_switch disc` | if-tree where the `R` arm uses an early `ReturnNode`; merge = `M` | merge = `M` regardless of layout; I1 |
| **Q3** | disc if-tree, then `scf.index_switch` with `body` in case 0 (once) | selector `IfOp` (`a‖b`), then `scf.if disc { body }` (once) | `body` emitted once; I2 |

## The one legitimate divergence: early return / throw

For **Q2**, MLIR synthesizes a discriminator + `scf.index_switch` to linearize
the `R: return` path, because `scf` regions are single-exit and cannot represent
an early `return`. Our target IR is *more permissive*: a `ReturnNode` (and a
`throw`/unreachable region-exit) is a valid branch-region terminator, so we nest
the `return 999` directly in the else arm and need no discriminator for the
return case. RESEARCH_ANSWER.md Q2 notes this is exactly why the MLIR pass is
named *lift* (not *convert*): with multiple return-like ops it leaves a residual
`cf.switch`. Both forms are semantically equal (the Q2 roundtrip returns
`100/200/999` correctly); ours simply exploits a representation MLIR's target
lacks.

The discriminator + N-way switch (`scf.index_switch`) IS our edge multiplexer —
needed when the multi-entry continuation carries *values* that must be selected
by which arm was taken (Q3, and N-entry merges/irreducible headers in general),
not for early returns.
