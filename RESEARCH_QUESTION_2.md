# Research hand-off #2: is `CFGToSCF` the right model, and how should we handle multi-entry control flow?

> **This document is self-contained.** You do not need access to the IRStructurizer.jl
> repository. Everything about "our implementation" is inlined in §A–§B. Answer §C from
> public primary sources (§D). Favor **exactness over breadth** — one airtight, fully-cited
> answer per question beats several vague ones. Cite **file:line** for LLVM/MLIR source and
> **section/DOI** for papers; "approximately" is not useful.

## A. What we're building, and the decision this research informs

We maintain **IRStructurizer.jl**, a compiler pass that converts a function's **unstructured
SSA control-flow graph** (basic blocks joined by conditional/unconditional gotos, with SSA
`phi` nodes at merges) into **nested structured control flow**. Our target IR has exactly
four control ops, and — this is the load-bearing detail — **every one of them carries
explicit values** (it is an SSA-`phi` → explicit-block-argument conversion, MLIR-style):

- `IfOp(cond, then_region, else_region)` — each region ends in `yield v…`; the yielded values
  become the `IfOp`'s SSA results.
- `LoopOp(body, init_values)` — a generic loop. The body runs with **block arguments**
  (loop-carried values) and ends in `ContinueOp(vals)` (iterate with new carried values) or
  `BreakOp(vals)` (exit with results).
- `WhileOp` (condition-at-top) and `ForOp` (counted) — higher-level loop forms recognized in
  a **separate downstream post-pass** over `LoopOp`. The core algorithm never emits these.

So our target is **nested regions that yield/carry values** — the same shape as MLIR's `scf`
dialect (`scf.if`/`scf.while`/`scf.for` with results) or RVSDG region nodes. It is **not**
block/label/`br`-style structured control (WebAssembly's `block`/`loop`/`br`), and **not**
predicated linear flow (execution masks). That distinction is the crux of question C1.

We rewrote the core to follow **MLIR's `CFGToSCF` pass** (Markus Böck's upstream
"ControlFlow → SCF lifting" / `--lift-cf-to-scf`, implementing Bahmann, Reissmann, Jahre &
Meyer 2015). We have **already realized and verified** the following pieces of that algorithm:

- **Continuation by exclusion** — the merge after a conditional is the single distinct target
  of edges leaving the branch region, never chosen by block-index ordering.
- **Edge-domination branch split** — a successor's region is its dominated subtree only when
  that successor's sole predecessor is the conditional block.
- **No node duplication** — we never clone a subtree into sibling branches.
- **Region-exit uniformity** — a `return` or a `throw`/unreachable dead-end (a block with no
  successors) is re-materialized in place, not dropped.
- **Reduce form** — a single "defined-inside / used-outside" escape sweep promotes escapees
  to loop-carried/yielded values.
- **Loop-form layering** — the core emits only the generic `LoopOp`; `WhileOp`/`ForOp`
  recognition is strictly downstream.

**The one remaining gap — and the reason for this research — is the *edge multiplexer*.** In
`CFGToSCF` a single `EdgeMultiplexer` construction (one new block with per-entry argument
ranges, a discriminator argument, `undef`/`poison` fill for inactive entries, and a `switch`
dispatch) is the universal mechanism for every multi-entry / multi-predecessor situation:
multi-entry (irreducible) loop headers, multi-exit loop latches, and multi-predecessor branch
continuations. **We have realized this only for the 2-entry short-circuit case** (a
boolean-discriminator `if`), via a pattern-matcher with explicit dominance/closure/escape
conditions — and it has corner cases (nested guarded bodies inside a loop are unsupported).
We currently **reject irreducible CFGs outright** (multi-entry strongly-connected components;
in our source language these arise only from `@goto`), failing loudly rather than lifting them.

We are about to invest in closing this gap, and want the research to settle three decisions
**before** we commit to an architecture:

1. **Model.** Is `CFGToSCF`/Bahmann genuinely the right algorithm for a *value-yielding
   nested-region* target, or is a different published algorithm a better fit?
2. **Mechanism.** For irreducible CFGs and multi-entry continuations, is the **edge
   multiplexer** (discriminator dispatch, no duplication) the right choice over **controlled
   node-splitting / tail duplication** — and under what conditions, if any, would we prefer
   splitting?
3. **Architecture.** Should the multiplexer be applied as a **CFG-mutation pre-pass** (insert
   dispatch blocks, redirect edges, *then* lift a now-single-entry CFG) or built directly by
   an **analyze-and-build** recursive walk (our current architecture)?

## B. Concrete constraints that should shape the answer

- **No node duplication is a hard requirement** for us (it is also `CFGToSCF`'s stated design
  goal). An approach is only acceptable if duplication is, at worst, an *optional* late
  optimization layered on a duplication-free core.
- **The target dialect may lack a native multi-way switch.** Our `IfOp` is two-way only; an
  N-way discriminator dispatch must lower to a **compare chain of nested `IfOp`s** (or we add
  a switch op). We need to know whether that changes the soundness or cost story.
- **Values must thread correctly across a synthesized merge/dispatch**, including `undef`/
  `poison` on edges where a value is not defined. We need the exact correctness conditions.
- **Multiple return-like exits** (a region with both `return` and `throw`, or several
  returns) — our IR *can* represent early `return`/`throw` as a region terminator, unlike
  pure `scf`. We want to know whether that lets us avoid machinery that pure-`scf` lifting needs.

## C. Questions

For each: a precise answer, a citation, and a concrete verdict (not a survey).

### C1 — Is `CFGToSCF`/Bahmann the right model for a value-yielding nested-region target?
Classify each algorithm below by **(a)** the target it produces — value-yielding nested
regions (SCF/RVSDG-like) vs. block/label/`br` structured control (WASM-like) vs. predicated
linear flow — and **(b)** whether it is duplication-free. Then give a verdict: is any of them
a *better* fit than `CFGToSCF` for our four-op, value-carrying target, or does `CFGToSCF` win?
- **Relooper** (Alon Zakai, Emscripten; "Emscripten: an LLVM-to-JavaScript compiler").
- **Norman Ramsey, "Beyond Relooper: recursive translation of unstructured control flow to
  structured control flow"** (ICFP 2022, DOI 10.1145/3547621).
- **LLVM WebAssembly backend**: `WebAssemblyFixIrreducibleControlFlow` and CFGStackify.
- **LLVM `StructurizeCFG.cpp`** (AMDGPU) — predicate/flow-block linearization.
- **RVSDG line**: Bahmann/Reissmann "Perfect Reconstructability…" (TACO 2015, DOI
  10.1145/2693261) and the `jlm`/RVSDG and `numba-rvsdg`/`numba-scfg` implementations.

### C2 — Edge multiplexer vs. controlled node-splitting (the central mechanism choice)
`CFGToSCF` restores single-entry via a discriminator-dispatch **edge multiplexer** with no
duplication. The classical alternative restores reducibility/single-entry via **controlled
node splitting** (Janssen & Corporaal, "Making Graphs Reducible with Controlled Node
Splitting," ACM TOPLAS 1997, DOI 10.1145/267959.269971; cf. Cocke–Miller). For each:
- When is it preferred, per the literature?
- Exact costs: multiplexer = one discriminator value + `undef`/poison fill + an N-way switch
  (or compare chain) + one extra loop-carried value per merged entry, executed every
  iteration for loop headers; node-splitting = code-size blowup, **worst-case exponential**
  in pathological irreducible CFGs (cite the bound). Confirm or correct these.
- Is there a **principled hybrid** — multiplexer for correctness, then *optionally* duplicate
  only small, side-effect-free tails as a downstream optimization? Does any production
  compiler do this, and on what threshold?
- **Verdict:** for a duplication-averse, value-yielding target, is there ever a reason to
  prefer splitting over the multiplexer?

### C3 — Is "one multiplexer construction for all three roles" real and sound?
Confirm whether mature implementations use the **same** edge-multiplexer construction,
parameterized only by the edge set (and extra args), for **(i)** multi-entry irreducible loop
headers, **(ii)** multi-exit loop latches (the `shouldRepeat` flag), and **(iii)**
multi-predecessor branch continuations — or whether they special-case these. We intend to
unify all three behind one mechanism and want to know if that is sound and standard, or if
some role needs distinct treatment.

### C4 — Architecture: mutate-then-lift vs. analyze-and-build
Does `CFGToSCF` (and its peers) physically **mutate the CFG** — insert the dispatch/mux
blocks and redirect predecessor edges, then run the structured lifting over the now
single-entry CFG — or does it **build the structured output directly** from a read-only
dominance/SCC analysis? Pin this with citations (which functions mutate, which read). Then
give a recommendation: for a value-yielding SCF target with a strict no-duplication
invariant, which architecture is more maintainable and less prone to multi-entry corner
cases — a CFG-mutation pre-pass that normalizes to single-entry before a simple lift, or a
recursive analyze-and-build walk that handles multi-entry inline?

### C5 — Soundness pitfalls of the multiplexer / reduce-form approach
What has bitten implementers? In particular:
- **`undef`/poison fill** on edges where a carried value is not defined / does not dominate
  the latch — exact correctness condition, and what goes wrong if it's mis-set.
- **Discriminator** representation and dispatch when the target has **no native switch** (a
  nested compare chain): any soundness or determinism concerns.
- **Phi/block-argument unification** across entries with differing argument sets.
- **Multiple return-like exits**: `CFGToSCF` is named "lift" (not "convert") because it
  *cannot always* eliminate all control flow — when a region has several return-like op
  kinds it leaves a residual `switch`. Explain that limitation precisely. Does a target that
  permits early `return`/`throw` as a region terminator (ours does) sidestep it, and how far?

## D. Primary sources (read in this order; cite specifics)
1. **MLIR `CFGToSCF`** in `llvm/llvm-project`: `mlir/lib/Transforms/Utils/CFGToSCF.cpp`
   (`EdgeMultiplexer`, `createSingleEntryBlock`, `transformCyclesToSCFLoops`,
   `transformToStructuredCFBranches`, `createSingleExitingLatch`) and the header-comment
   prose + ASCII diagrams in `mlir/include/mlir/Transforms/CFGToSCF.h`. Plus the original
   review (D156889) and Markus Böck's EuroLLVM 2024 talk "Lifting CFGs to Structured Control
   Flow in MLIR."
2. **Bahmann, Reissmann, Jahre, Meyer**, "Perfect Reconstructability of Control Flow from
   Demand Dependence Graphs," ACM TACO 11(4), 2015 (DOI 10.1145/2693261) — §4.1 Loop
   Restructuring, §4.2 Branch Restructuring.
3. **Ramsey**, "Beyond Relooper," ICFP 2022 (DOI 10.1145/3547621).
4. **Janssen & Corporaal**, "Making Graphs Reducible with Controlled Node Splitting," ACM
   TOPLAS 19(6), 1997 (DOI 10.1145/267959.269971).
5. **Zakai**, "Emscripten" (Relooper); LLVM `WebAssemblyFixIrreducibleControlFlow.cpp` and
   CFGStackify; LLVM `llvm/lib/Transforms/Scalar/StructurizeCFG.cpp` (read to *contrast* — it
   is predicate/flow-block, the model we are NOT following).
6. RVSDG implementations for the value-yielding-region comparison: `jlm`, `numba-rvsdg`.

## E. Deliverable
A markdown report answering C1–C5, each with citation and a concrete verdict. The three
outputs that decide our next move:
- **(a)** Keep `CFGToSCF` as our model — yes/no, and if no, what instead.
- **(b)** The mux-vs-split decision, with the exact conditions (if any) under which splitting
  would be preferable for a duplication-averse value-yielding target.
- **(c)** A recommendation on **mutate-then-lift vs. analyze-and-build** architecture, with
  the reasoning tied to maintainability and multi-entry corner-case avoidance.
