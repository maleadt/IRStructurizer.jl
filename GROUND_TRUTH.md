# Ground Truth: the review oracle for structurization PRs

Decide whether a structurization PR *converges* on the principled CFGToSCF algorithm
(Bahmann et al. 2015, as realized in MLIR's `CFGToSCF.cpp`) or *diverges* into ad-hoc,
pattern-keyed corner-case handling. Authority for the exact MLIR predicates: `RESEARCH_ANSWER.md`.
Roadmap and current status: `PLAN.md`. This file is the checklist you apply to a diff.

> **North star (the target).** Every *reducible* CFG is structurized by two recursive
> transformations — *lift cycles* (natural loops → `LoopOp`) and *lift branches* (dominance →
> `IfOp`) — where the conditional's **continuation is defined by exclusion** and a single
> **edge multiplexer** handles every multi-entry / multi-predecessor situation. No pattern
> templates, no block-numbering heuristics, no node duplication.

> **Realized vs. target (read this before judging a PR).** Three of the four pillars hold:
> continuation-by-exclusion ✓, layout independence ✓, no node duplication ✓. The fourth — *a
> single edge multiplexer* (I4) — does **not** hold yet: it exists only as a 2-entry
> short-circuit handler (`find_gated_body`), which is itself a shape template with corner
> cases, and irreducible CFGs are **rejected**. Closing that gap (§3) is the work that takes
> us from "mostly principled" to "principled". A PR is on the right track when it shrinks §3.

---

## 1. Invariants (the testable contract)

Properties the algorithm and its output must satisfy. Most can be made into an assertion.

| # | Invariant | How to check | Status |
|---|-----------|--------------|--------|
| **I1** | **Layout independence.** Output depends only on CFG + (post)dominance, never on block *numbering*. | No `sort!` over block indices in a control decision; permute non-semantic block order → identical structure. | **Holds.** The `sort!` merge tie-break is gone; guarded by the Q2 two-layout test. |
| **I2** | **No node duplication.** Each source statement appears once (a fresh `ssa_remap` index is a *rename*, not a copy). Reducible CFGs never require duplication. | Count emitted occurrences of each source SSA def. | **Holds.** `tail_duplicate_branch!` was deleted (#48); guarded by the Q3 "body once" test. |
| **I3** | **Continuation by exclusion.** The `IfOp` merge is the single distinct target of edges leaving the branch, never picked from a list by order. | Merge selection has no block-index tie-break. | **Holds.** `find_branch_regions` uses `branch_continuation`. |
| **I4** | **One mechanism for many predecessors.** Multi-entry loops, multi-exit loops, and multi-predecessor merges all go through *the edge multiplexer*, not per-shape guards. | Each "merge"-flavored case routes through one multiplexer. | **PARTIAL — the open invariant.** Realized only for 2-entry short-circuits (`find_gated_body`); irreducible rejected; nested gated bodies unsupported. |
| **I5** | **Reduce form captures escapees uniformly.** Every value defined in a region and used outside becomes a carry/yield via one escape sweep — no per-use-site casing. | New "value escapes" cases extend the *enumeration* (`stmt_ssa_uses`, `find_extra_exit_values`), not a branch. | **Holds.** Single sweep; `PiNode`/`:invoke` are enumeration entries, not paths. |
| **I6** | **Core emits only generic loops.** `WhileOp`/`ForOp` recognition lives entirely in `promote_loops!`; the core walk never inspects counting/condition patterns. | No condition/step/`iterate` matching in `walk.jl`/`loops.jl`. | **Holds.** Guarded by the `promote=false` test. |
| **I7** | **Semantics preservation (empirical).** structurize → unstructurize → execute equals direct execution, for every corpus function. | `@roundtrip` (`test/corpus.jl`, `test/runtests.jl`). | **Holds** for the corpus. The hard stop. |
| **I8** | **No silent control-flow loss.** Every edge/terminator (throws, early returns, dead-ends) is represented or provably equivalent; nothing is dropped to make a region fit. | Validators + roundtrip on throw/early-return cases. | **Holds** for known shapes; region-exits (return *and* throw) are re-materialized uniformly. |

I7 is the executable ground truth. I1–I6, I8 are the structural ground truth that explain
*why* a roundtrip can pass today yet break on the next CFG shape. **I4 is where the remaining
risk lives** — a green corpus does not prove a new multi-entry shape is handled.

---

## 2. The review litmus test

For each hunk touching `src/structurize/`, classify it:

- **(A) Heuristic → structural.** Replaces an ordering/layout/type guess with a
  dominance/post-dominance/exclusion computation. → **Converging. Favor.**
- **(B) Completes a general mechanism.** Adds a missing case to an *enumeration* meant to be
  exhaustive (`stmt_ssa_uses` gaining `PiNode`; the multiplexer gaining N-entry support). →
  **Converging. Favor.**
- **(C) Pure robustness.** Bounds check, undef-guard, type widening, debug-info anchor —
  orthogonal to the principle. → **Neutral.**
- **(D) New pattern-keyed branch.** An `if <syntactic shape>` (short-circuit, throw,
  "sequential ifs", block-order tie-break) that exists only to make one CFG family work. →
  **Diverging. Scrutinize.** Which invariant is being worked around, and what would removing
  the underlying heuristic cost instead?
- **(E) Guard on a heuristic.** Narrows an existing deviation so the symptom stops, leaving
  the heuristic in place. → **Diverging (debt).** The most common failure mode: small and
  safe-looking, but it deepens dependence on the approximation it guards.

A PR moves the wrong way when its center of mass is (D)/(E) — the *fix* is a new conditional
keyed on input shape rather than a correction to a structural computation. A PR is healthy
when (D)/(E) hunks name the invariant they defer and note it in §3, and when (A)/(B) hunks
shrink §3.

**Grep the diff for:** new `sort`, block-index comparisons in control decisions, function or
flag names containing a shape (`short_circuit`, `is_throw`, `gated`, `sequential`), and new
top-level `if`/`elseif` arms in `find_branch_regions`, `emit_branch!`, `find_gated_body`,
`find_loop_exit`. Each is a candidate (D)/(E).

---

## 3. Current state — what's principled, what's a residual heuristic

A PR should *shrink* this section; growing or adding a row is debt (note it) or a regression
(scrutinize per §2).

**Closed / aligned (with regression guards):**

- **Merge selection** — continuation by `branch_continuation` exclusion singleton; no
  `sort!` tie-break (I1, I3). *Was D-merge.*
- **Pass-through absorption** — gone; exclusion finds the real merge directly (I3, I4).
  *Was D-absorb.*
- **Branch-region split** — single-predecessor (edge-domination) gate, matching MLIR (I3).
  Guarded by the Q1 test. *Was D-split.*
- **Shared-tail duplication** — gone; the 2-entry multiplexer emits the tail once (I2).
  Guarded by the Q3 test. *Was D-dup.*
- **Region exits** — a `return` or `throw` block (`numSuccessors == 0`, MLIR's
  `isRegionExitBlock`) reached as a *secondary* exit is re-materialized in place, not dropped
  to a bare break (I8). `is_region_exit`, not the old `Union{}`-only `is_throw_exit`.
  *Was D-throw (closure side).*
- **Irreducible CFGs lifted, not rejected (D-mux)** — `normalize_cf` (mutate-then-lift,
  `src/structurize/multiplex.jl`) inserts one `EdgeMultiplexer` per multi-entry SCC: the entry
  blocks collapse to a single loop header that dispatches on a discriminator carry, and a latch
  unifies the back edges, yielding a plain reducible `LoopOp`. `check_irreducible` is now a
  backstop (should never fire), not a rejection. Guarded by the D-mux corpus testset (the `@goto`
  examples, N=2 and N=3 entries). *Was D-mux.* **This is the first half of I4** (one mechanism for
  many predecessors); the continuation half (`find_gated_body`) is still open below.

**Open — the remaining ad-hoc surface, in priority order:**

| Gap | Where | What's ad-hoc | Principled end state | At risk |
|-----|-------|---------------|----------------------|---------|
| **The multiplexer's continuation case is a 2-entry shape-matcher** | `find_gated_body` (`loops.jl`) | Identifies a gateable body by explicit dominance + closure + single-escape conditions. Fails on shapes it can't pattern-match — **nested gated bodies in a loop are unsupported** (fail loudly via SSA validation). | Route multi-pred continuations through the *same* `EdgeMultiplexer` (now built — `multiplex.jl`) upfront, so the lift sees single-entry continuations and `find_gated_body` is deleted. | **I4** |
| **Primary loop-exit selection** | `find_loop_exit`, `find_extra_exit_values` (`loops.jl`) | The primary exit is the back-edge-adjacent exit (topology + dominance only, layout-independent); the escape sweep seeds from it. A residual preference for *which* exit is primary remains (no exit is dropped — I8-safe). | Single-exiting latch via the multiplexer over all exit edges (no "primary" choice). | I4 (minor, M4) |

The first two collapse into **one** change — a uniform N-entry edge multiplexer (MLIR's
`EdgeMultiplexer`) — which would delete `find_gated_body`, fix nested gated bodies, and lift
irreducible CFGs together. It is the single highest-leverage convergence left. In the current
*recursive-walk* architecture (we build structured ops directly over an immutable `IRCode`),
realizing it likely means one of: (a) a **CFG-mutation pre-pass** that inserts mux blocks and
redirects entry edges, MLIR-style, so the walk then sees only single-entry regions; or (b)
generalizing `find_gated_body`'s discriminator-as-yield trick to N entries *within* the walk.
Which is tractable is an open **design** question (see PLAN.md / §"research" below), not a
literature gap.

---

## 4. The executable corpus

`test/corpus.jl` is the artifact you run against a PR — one `@testset` per family above plus
the Q1/Q2/Q3 divergence CFGs (built as synthetic IR with structural assertions: merge = T,
merge = M under two layouts, body emitted once) and the I6 `promote=false` guard.
`test/goldens/` holds `mlir-opt --lift-cf-to-scf` reference output for Q1/Q2/Q3.

Rules: every PR keeps the corpus green (I7/I8, non-negotiable). A PR that fixes a new CFG
shape **adds that shape, tagged** — if it maps to an open §3 gap, it's a witness the gap is
load-bearing; if it needs a new tag, that may be a new deviation. Prefer structural
assertions (count statements, assert the chosen merge) over execution-only, so I1–I4 are
checked directly and not only through the I7 keyhole — execution can pass while structure
relies on a layout coincidence. **The corpus did not catch the two latent miscompiles fixed
on this branch** (early-return-in-loop; gated-body-throwing-out-of-loop); both were found by
*fuzzing* the families with exec-vs-direct comparison. Fuzz new multi-entry shapes before
trusting I4.
