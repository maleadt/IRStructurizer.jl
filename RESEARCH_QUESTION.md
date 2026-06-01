# Research hand-off: pin down MLIR CFGToSCF's exact structural definitions

> **This document is self-contained.** You do not need access to the IRStructurizer.jl
> repository to answer it. All context you need about "our implementation" is inlined in
> §B below. The questions themselves (§C) are answered from public primary sources (§D).

## A. What we're doing and why this matters

We maintain **IRStructurizer.jl**, a compiler pass that converts a function's unstructured
SSA control-flow graph (basic blocks connected by conditional/unconditional gotos, with
SSA `phi` nodes at merge points) into **nested structured control flow** — the target IR
has exactly four control ops:

- `IfOp(cond, then_region, else_region)` — structured if/else; each region `yield`s values.
- `LoopOp(body_region, init_values)` — a general loop. The body runs with **block
  arguments** (loop-carried values); it ends in `ContinueOp(vals)` (iterate again with new
  carried values) or `BreakOp(vals)` (exit with results). This is the generic loop form.
- `WhileOp` / `ForOp` — higher-level loop forms recognized in a **separate post-pass** from
  `LoopOp` (condition-at-top while; counted for). The core algorithm never emits these.

Values that flow out of a region are made explicit: branch regions `yield` merge values;
loops carry/break values through block arguments. (This is the SSA-`phi` → explicit
block-argument conversion, MLIR-style.)

We rewrote the core to follow **MLIR's CFGToSCF pass** (based on Bahmann et al. 2015),
replacing an older pattern-template approach. The intended algorithm is two recursive
transformations applied to single-entry regions:

1. **Lift cycles**: detect cycles (SCCs / natural loops), turn each into a structured loop.
2. **Lift branches**: at a conditional, recurse into each successor's region, with a
   **continuation region** after the conditional reconverges.

Our implementation is faithful in outline but **substitutes heuristics for two of the
algorithm's exact structural computations**. We want to know precisely what MLIR does so we
can replace our heuristics with the exact constructions — and so we can tell, when reviewing
future patches, whether a fix converges on the real algorithm or drifts into ad-hoc special
cases. **The most valuable output of this research is minimal CFG counterexamples where our
heuristic diverges from the exact algorithm** (see §B for the heuristics, §C for the asks).

## B. What our implementation currently does (the heuristics to compare against)

Construct your counterexamples (§C) against these. Each is described concretely so you can
reason about it without our source.

- **H-split — branch region membership.** At a conditional in block `E` with successors
  `T` (true) and `F` (false), we assign to the *then* region "all blocks **dominated by
  `T`**" and to the *else* region "all blocks **dominated by `F`**", then remove any
  overlap by set difference. We suspect this is *not* the same as MLIR's notion of "blocks
  solely reachable through the edge `E→T`," and that they diverge on some CFG.

- **H-merge — continuation/merge selection.** We pick the conditional's merge (continuation)
  block as the **immediate post-dominator** of `E` when one exists. When it does **not**
  exist — e.g. some successor path ends in `return`/`throw`, so the only post-dominator is
  the virtual exit — we fall back to: collect candidate reconvergence blocks, **sort them by
  basic-block index, and take the first**. This block-numbering tie-break is layout-
  dependent and we want to eliminate it.

- **H-dup — shared tails / short-circuit.** For short-circuit conditions (`if a || b`,
  `if a && b`) and other cases where a block is reachable from *both* branches, our
  dominance-based splitting can't place that shared tail in a single region, so we currently
  **duplicate** it: we clone the shared dominator subtree into each sibling branch (with
  fresh SSA names). We believe MLIR avoids all node duplication via an **edge multiplexer**
  and want the exact alternative construction.

- **H-throw — throw/unreachable exits.** When a loop or branch has a successor that is a
  dead-end `throw`/`unreachable` block, our exit-selection heuristic *prefers a non-throw
  continuation and skips the throw successor*, which risks dropping it; we then need
  special-case code to re-materialize throws. We expect MLIR treats a throw/unreachable
  block as an ordinary region ending in an unreachable terminator, handled uniformly with no
  special case.

- **H-mux — irreducible CFGs.** We currently **reject** irreducible control flow (cycles
  with multiple entry blocks, e.g. from `@goto`). MLIR handles these with an entry
  multiplexer. We want to confirm this is the *same* multiplexer construction as H-dup's, so
  future N-entry support is a generalization rather than a new code path.

## C. Questions

For each, give the precise definition/construction with a **file:line or section citation**,
and for Q1–Q3 a **minimal CFG counterexample** (ASCII block diagram + edges) where our
heuristic from §B diverges from the exact MLIR algorithm.

### Q1 — Branch region membership (vs H-split)
- What is MLIR's exact predicate for which blocks belong to a conditional successor's
  region? State precisely "blocks solely dominated by the **edge** `E→T`" (or whatever the
  real criterion is) and how it differs from "blocks dominated by the **block** `T`."
- Give a minimal CFG where "dominated by `T`, minus overlap" (H-split) assigns a block
  differently than the exact edge-based criterion.

### Q2 — Continuation by exclusion (vs H-merge)
- How does MLIR determine the continuation region after a conditional? Confirm whether it is
  defined purely by **exclusion** (blocks dominated by `E` but not solely-dominated by any
  single successor) and therefore needs **no** ordering/tie-break.
- Critically: what does MLIR do when a successor path ends in `return`/`unreachable` so
  there is no real post-dominator (only the virtual exit)? This is exactly where we fall
  back to sort-by-block-index. Show that MLIR's handling is deterministic and
  layout-independent, and give a CFG where our sort-based pick is fragile.

### Q3 — The edge multiplexer (vs H-dup and H-mux)
- Give the exact construction of MLIR's edge multiplexer: what block arguments it adds, how
  the discriminator value is encoded and dispatched (switch? compare chain?), how unused
  arguments are filled, and how incoming edges are redirected to it.
- Explain **why this makes node duplication unnecessary** for shared merge tails and
  short-circuit patterns — i.e. how the shared tail is emitted exactly once. Contrast with
  our H-dup tail-duplication and give a short-circuit CFG (`if a || b { body }`) showing the
  multiplexer's single-emission result vs our duplicated result.
- Confirm the **same** multiplexer mechanism serves all three roles — multi-entry loop
  (irreducible), multi-exit loop, and multi-predecessor merge — and show the unifying view.

### Q4 — Reduce form (loop-carried value capture)
- Exactly which values does cycle-lifting promote to loop-carried, and how are they
  enumerated? Confirm it is a single escape-analysis sweep ("defined inside the cycle, used
  outside") with no per-use-kind special cases, and describe how `undef`-initialized carried
  values are introduced for values that escape on only some paths.

### Q5 — Loop form layering (vs our post-pass)
- MLIR emits do-while (condition-at-latch) loops from the core. Confirm that *all*
  higher-level loop recognition (rotating to condition-at-top "while", recognizing counted
  "for") is **downstream** of CFGToSCF and not part of it. (This validates our keeping
  while/for recognition as a strict post-pass over the generic loop op.)

### Q6 — Determinism and irreducibility
- Is MLIR's output invariant under basic-block **renumbering** — i.e. does it depend only on
  the CFG topology + dominance/post-dominance, never on block index order? Cite where (if
  anywhere) ordering legitimately enters.
- For irreducible CFGs with **N > 2** entry blocks, confirm the entry multiplexer is the
  *same* construction as Q3 (one mechanism, parameterized by N), not a separate algorithm.

## D. Primary sources (public)

Read in order of authority; cite specifics.

1. **MLIR `CFGToSCF`** in the LLVM monorepo (github.com/llvm/llvm-project):
   - `mlir/lib/Transforms/Utils/CFGToSCF.cpp` — the implementation. Read
     `transformCyclesToSCFLoops`, `transformToStructuredCFBranches`, the `EdgeMultiplexer`
     class, and the single-exit-latch / reduce-form helpers.
   - `mlir/include/mlir/Transforms/CFGToSCF.h` — the ~100-line header comment with ASCII
     diagrams is the canonical prose description of the algorithm.
2. **Bahmann, Reissmann, Jahre, Meyer**, "Perfect Reconstructability of Control Flow from
   Demand Dependence Graphs," *ACM TACO* 11(4), 2015 — the formal framework and correctness
   argument behind the pass.
3. **LLVM `StructurizeCFG.cpp`** (`llvm/lib/Transforms/Scalar/StructurizeCFG.cpp`) — read
   only to *contrast*; it is a different (predicate/flow-block) approach and is **not** our
   model. Note key differences if helpful.

## E. Deliverable

A markdown report structured Q1–Q6. For each: the precise definition/construction, a
citation, and (Q1–Q3) the minimal divergence CFG. We will turn the divergence CFGs into
regression tests, so prefer one airtight, fully-specified example over several vague ones.
Favor exactness over breadth — "approximately" is not useful here.
