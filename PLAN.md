# PLAN — Complete the principled CFGToSCF alignment

**Audience:** an engineer/agent picking up IRStructurizer.jl with no prior conversation
context. This is the implementation brief. It assumes the companion docs in this repo are
available and references them instead of repeating their content:

- **`CLAUDE.md`** — repo overview, public API, architecture, how to run tests.
- **`GROUND_TRUTH.md`** — the *review oracle*: invariants I1–I8, the 5-way litmus test for
  judging a change (A/B converge, C neutral, D/E diverge), and the deviation watch-list.
  **Read this first** — it is the standard every change here is held to.
- **`RESEARCH_QUESTION.md`** + **`RESEARCH_ANSWER.md`** — the exact MLIR `CFGToSCF`
  definitions (continuation-by-exclusion, edge multiplexer, reduce form) with
  `CFGToSCF.cpp` line citations and minimal divergence CFGs. This is the **authority** for
  what "principled" means; cite it when in doubt.
- **`TODO.md`** — background note on irreducible CFGs (`@goto`) and the multiplexer.

The north star (from `GROUND_TRUTH.md`): *every reducible CFG is structurized by two
recursive transformations — lift cycles (natural loops → `LoopOp`) and lift branches
(dominance → `IfOp`) — where the conditional's continuation is defined by **exclusion**
(everything not solely dominated by a branch successor) and the **edge multiplexer** is the
single mechanism for every multi-entry / multi-predecessor situation. No pattern templates,
no block-numbering heuristics, no node duplication.*

## Orientation: the code

Entry point `src/structurize.jl` → `structurize(ir)`:
1. `check_irreducible(ir)` (`src/structurize/cfg.jl`) — currently **throws** on multi-entry
   SCCs.
2. `StructurizeCtx` holds `domtree`, `postdomtree`, `loop_map` (natural loops), the SSA
   counter, `types`, and `ssa_remap` (the reduce-form rename dict).
3. `structurize_region!` (`src/structurize/walk.jl`) — the recursive walk. Emits block
   statements, dispatches terminators, lifts loops (`emit_loop!`) and branches
   (`emit_branch!`). A `LoopCtx` makes the walk loop-aware (back-edge → `ContinueOp`, exit →
   `BreakOp`).
4. `src/structurize/loops.jl` — branch-region splitting (`find_branch_regions`), the
   MLIR-style `branch_continuation`, the short-circuit detector `find_gated_body`, loop phi
   extraction, and reduce-form escape analysis (`find_extra_exit_values`, `stmt_ssa_uses`).
5. `promote_loops!` (`src/structurize/promote.jl`) — post-pass: `LoopOp` → `WhileOp` →
   `ForOp`. The core never emits While/For.
6. Output types/validation/printing live in `src/ir/`. Validation
   (`src/ir/validation.jl`) is your safety net — keep all validators passing.

**Run the tests:** `julia --project -e 'using Pkg; Pkg.test()'` (≈20s once precompiled,
618 tests as of the #48 baseline). `@roundtrip f(args...)` (in `test/runtests.jl`)
structurizes → unstructurizes → executes and compares to direct execution — this is
invariant **I7**, the executable ground truth. **Do not `git push`**; land work as local
commits for the maintainer to ship.

## Baseline: PR #48 is merged (Phase 0 — DONE)

`main` now contains six correctness fixes (each a separate commit, authored upstream):
1. Sequential branches sharing a condition (pass-through absorption gated on single
   successor; lattice types widened to concrete `Type`s).
2. **Short-circuit-guarded bodies via an MLIR edge multiplexer** — adds `branch_continuation`
   + `find_gated_body` + `emit_gated_branch!`, and **deletes `tail_duplicate_branch!`**.
3. `UndefRefError` fix on an undef phi slot in `find_gated_body`.
4. Thread `PiNode`-referenced loop values out as exit values (`PiNode` added to
   `stmt_ssa_uses`).
5. Count the `:invoke` callee (`args[2]`) as a use.
6. Preserve an in-loop `throw` instead of dropping it to a bare break (`is_throw_exit`).

## State after #48, vs. the principle (the gap this plan closes)

Two corrections to prior assumptions, verified against the merged code:

- **D-split is already MLIR-aligned.** `find_branch_regions` (`loops.jl:13`) only collects a
  successor's dominated subtree when `count_non_backedge_preds(succ) == 1` — that
  single-predecessor gate *is* MLIR's edge-domination test (`RESEARCH_ANSWER.md` Q1,
  `CFGToSCF.cpp:981`). The Q1 counterexample does not miscompile today. Only a regression
  test is owed.
- **#48 built the principled primitive but wired it as a special case.**
  `branch_continuation` (`loops.jl:108`) is a faithful port of continuation-by-exclusion
  (`RESEARCH_ANSWER.md` Q2). But it is called **only** by `find_gated_body` (`loops.jl:170`),
  which fires **only** for the 2-entry short-circuit shape. The *main* merge decision in
  `find_branch_regions` still uses `ipdom` then a `sort!(collect(candidates))` tie-break
  (`loops.jl:45-47` and `loops.jl:66`) — **D-merge is live**, and it violates
  layout-independence (I1).

**Watch-list status** (vs. `GROUND_TRUTH.md §3`):

| Deviation | Status after #48 | Closed by |
|-----------|------------------|-----------|
| D-split (edge vs block domination) | **Already aligned** (single-pred gate) | test in Phase 3/4 |
| D-dup (`tail_duplicate_branch!`) | **Closed** by #48 (multiplexer) | — |
| D-merge (`sort!`-by-index merge fallback) | **Live** — drives the core | **Phase 1** |
| D-absorb (pass-through absorption loop) | Gated, still a separate step | Phase 1 |
| special-case path (`find_gated_body`, 2-entry only) | **Live** — parallel to the core | **Phase 2** |
| D-mux (irreducible rejected) | **Live** — `check_irreducible` throws | **Phase 2** |
| D-throw (`is_throw_exit` special case) | **Live** — guarded special case | Phase 2 |

The remaining work is mostly *rewiring code #48 already introduced* into the universal
mechanism — not greenfield.

## The work, in phases

Ordered so each lands green and special cases collapse *into* the general mechanism rather
than being deleted blind. Each phase: goal → concrete steps (with post-#48 anchors) → exit
criterion. Hold every change to the `GROUND_TRUTH.md` litmus test.

### Phase 1 — Promote `branch_continuation` to *the* merge selector (retires D-merge / D-absorb; `RESEARCH_ANSWER.md` Rec. 2, Q2)
The principled computation already exists; make it the core decision instead of a detector.
1. Replace the merge-selection block in `find_branch_regions` — the `ipdom` pick at
   `loops.jl:45-47` and especially the fallback loop `for c in sort!(collect(candidates))`
   at `loops.jl:66` — with `branch_continuation`: `notContinuation = current ∪ then_blocks ∪
   else_blocks`; continuation = the distinct targets of edges leaving `notContinuation`
   (`branch_continuation` already computes exactly this). The merge is the single common
   target. Keep using `ipdom` only as a *non-ordering* check (post-dominance is a boolean,
   never a sort key — see `RESEARCH_ANSWER.md` Q2).
2. **Delete the `sort!(collect(candidates))` tie-break entirely** (`loops.jl:66`). After
   this, no block-index ordering drives any structural decision (I1).
3. Fold the **pass-through absorption** branch in `emit_branch!` (`walk.jl:243`, the
   `isempty(phis) && length(...succs) == 1` block) into the same exclusion computation: a
   no-phi single-successor merge is just a continuation edge that forwards; exclusion handles
   it without a separate "absorb" step.
4. When the continuation singleton doesn't exist or a branch region contains a region-exit
   (return-like) block, this is MLIR's "synthesize one continuation via the multiplexer and
   reprocess" case — wire it to the Phase 2 multiplexer (or, transitionally, keep the
   2-entry `emit_gated_branch!` path and generalize in Phase 2).
- **Exit criterion:** `find_branch_regions` returns a merge derived purely from
  topology+dominance; no `sort!` over block indices remains in the structurizer; the Q2
  divergence CFG (`RESEARCH_ANSWER.md` Q2: `E→{T,F}, F→{M,R}, R:return`) picks `M`
  regardless of block renumbering — add it as a renumbering-invariance regression test.

### Phase 2 — Generalize the multiplexer to N entries (retires the special-case path, D-mux, D-throw; `RESEARCH_ANSWER.md` Rec. 3, Q3/Q6)
Turn `emit_gated_branch!` from a 2-entry short-circuit handler into the one continuation
mechanism, mirroring MLIR's single `EdgeMultiplexer` (`CFGToSCF.cpp:225-358`) serving all
roles.
1. In `emit_branch!`, replace the `find_gated_body` gate (`walk.jl:215`) with the general
   rule: **if the continuation has >1 entry, route through the multiplexer**. Remove
   `find_gated_body`'s shape conditions (2-entry cap, body-dominance/closure checks) — the
   multiplexer doesn't need them.
2. Generalize `emit_gated_branch!` (`walk.jl:374`) from the hard-coded 2-way
   (`disc ∈ {true,false}`, `then`/`else`) to an **N-way discriminator** per
   `RESEARCH_ANSWER.md` Q3: one multiplexer block with per-entry argument ranges, one
   discriminator argument, `undef` fill for the other entries' slots, and a switch/compare
   dispatch. For N=2 it must reduce exactly to today's code so #48's short-circuit tests stay
   green.
3. **D-mux falls out (`RESEARCH_ANSWER.md` Q6 — same construction parameterized by N):**
   replace `check_irreducible`'s `throw` (`cfg.jl:54`) with routing a multi-entry SCC's
   entry edges through the N-entry multiplexer, yielding a single-entry loop the existing
   machinery structurizes. Keep irreducible loops as `LoopOp` (no While/For promotion). See
   `TODO.md` for the SCC-detection background.
4. **D-throw:** with continuation driven by exclusion, a `throw`/`unreachable` block is just
   a region-exit block (`numSuccessors == 0` = MLIR's `isRegionExitBlock`,
   `RESEARCH_ANSWER.md` Q2) that contributes no continuation edge and stays nested in its
   region. Re-examine whether the `is_throw_exit` special case (`walk.jl:138` and its two
   call sites) is still needed; the goal is that emitting a throw block's statements is the
   *default* region behavior, not a guarded exception. A residual guard, if any, should be
   one line, not a path.
- **Exit criterion:** `find_gated_body` is deleted; one branch-lifting path handles diamonds,
  short-circuits, N-way merges, and irreducible entries; the `if a||b {body}` CFG still emits
  `body` exactly once (assert statement count); an N>2-entry `@goto` irreducible CFG (see
  `TODO.md` for an example) roundtrips where it previously threw.

### Phase 3 — Confirm loop / reduce-form layering (`RESEARCH_ANSWER.md` Rec. 4, 5; mostly validation)
1. **Reduce form (Q4):** confirm `find_extra_exit_values` (`loops.jl:598`) + `stmt_ssa_uses`
   (`loops.jl:662`) is a single "defined-in-loop / used-outside" sweep with no per-use-kind
   branches. #48 added `PiNode`; audit for any other use-kind on a dedicated path and fold it
   into the enumeration. Verify `undef`-fill on non-dominating latch edges matches MLIR
   (`CFGToSCF.cpp:742-756`).
2. **Loop form (Q5):** no code change expected — verify the core emits only `LoopOp` and that
   all While/For recognition stays in `promote.jl` (`promote_loops!` at `promote.jl:20`,
   `try_promote_while` at `:459`, `try_promote_for` at `:547`). Record this as invariant I6
   so future changes don't leak loop recognition into the walk.

### Phase 4 — Lock it down with a golden corpus (`RESEARCH_ANSWER.md` Caveats; `GROUND_TRUTH.md §4`)
1. Build a labelled `@roundtrip` corpus, one tag per watch-list row plus the three
   `RESEARCH_ANSWER.md` divergence CFGs (Q1, Q2, Q3) and the easy baselines (diamond,
   short-circuit, sequential-ifs-in-loop, early-return, in-loop throw, counted for/while,
   PiNode carry, `:invoke` closure, irreducible).
2. **Golden structural files:** run each divergence CFG through `mlir-opt --lift-cf-to-scf`
   (available at `/opt/homebrew/Cellar/llvm/22.1.6/bin/mlir-opt`; LLVM 22.1.6 — research
   cited 23.0.0git but the predicates are stable) to capture reference structured output, and
   assert our output matches that *shape* (e.g. "`body` emitted once", "merge = M") — so
   I1–I4 are checked directly, not only through the I7 execution keyhole. One-time capture
   into checked-in `.mlir` golden files; not a CI build dependency.
3. Add the renumbering-invariance test (permute non-semantic block order → identical
   structure) as the standing guard for I1.
4. Update `GROUND_TRUTH.md §3`'s watch-list to mark D-split, D-dup, D-merge, D-absorb, the
   special-case path, D-mux, and D-throw as closed.

## Sequencing, risk, definition of done

- **Order:** Phase 1 → 2 → 3 → 4. Phases 1–2 are the substantive refactors; each is a
  rewiring of code #48 introduced, lowering risk. Consider doing Phase 4.1/4.2 (corpus +
  goldens) *before* Phase 2 so the N-entry rewrite has a tight net.
- **Biggest risk:** Phase 2's N-way multiplexer touches the hottest path. Mitigation: N=2
  must reduce exactly to #48's `emit_gated_branch!`, pinned by its existing tests; land
  behind the full corpus.
- **Definition of done:** the watch-list is empty; one branch-lifting path and one loop-
  lifting path with no shape-keyed special cases; no `sort!`-by-block-index anywhere; the
  litmus test *inverts* — a future PR that adds an `if <CFG shape>` branch to the lifter is
  no longer needed for correctness, so any such PR is a clear (D) regression signal. That
  reviewability is the whole point.

## Decisions (resolved by the maintainer)
1. **PR landing:** #48 merged to `main` as the integration of all pending fixes; #46/#47
   closed as subsumed (verified: #46 = #48's first three commits verbatim; #47 = #48's PiNode
   change, byte-identical, repositioned).
2. **Irreducible CFG (Phase 2.3): yes** — it falls out of the N-entry multiplexer at low
   marginal cost and removes the rejection path / D-mux entirely.
3. **`mlir-opt`: available** at `/opt/homebrew/Cellar/llvm/22.1.6/bin/mlir-opt` — Phase 4.2
   golden-file capture is a go.

## Implementation status (rework branch)

**Done.**
- **Phase 1 (D-merge, D-absorb): closed.** `find_branch_regions` derives the merge from
  `branch_continuation` (the exclusion singleton); the `sort!`-by-block-index tie-break and
  the pass-through absorption loop are deleted. No block-index ordering drives any structural
  decision (I1). The Q2 CFG picks `M` in two block layouts (renumbering test).
- **Phase 4.1–4.3: done.** `test/corpus.jl` is the standing net: a synthetic-IR builder pins
  Q1/Q2/Q3, with structural assertions (merge = T / M / body-once) + roundtrip; a tagged
  `@roundtrip` net per watch-list family; `test/goldens/` captures `mlir-opt --lift-cf-to-scf`
  reference output and documents the one legitimate divergence (we allow early `return`/`throw`
  as a branch terminator; `scf` must linearize via a discriminator switch). 697 tests total.
- **D-throw (Phase 2.4): converged.** `is_throw_exit` (which special-cased `Union{}` throws)
  is now `is_region_exit` = `numSuccessors == 0` (MLIR's `isRegionExitBlock`). A *secondary*
  region-exit — a `return` as much as a `throw` — is re-materialized in place; the loop's
  *primary* exit (threaded via `LoopCtx.exit_dest`) still breaks. This fixed a latent
  miscompile: early `return` inside a loop failed to structurize on the #48 baseline.
- **Phase 3 (I6 + reduce form): confirmed + guarded.** Added `promote=false` to
  `structurize`/`StructuredIRCode` and a test that the core emits only `LoopOp`
  pre-promotion (For/While live only in `promote.jl`). `stmt_ssa_uses` is a single
  enumeration (Q4 confirmed); no per-use-kind path needs folding.
- **Bonus bug fix.** A second latent silent miscompile (found by fuzzing the corpus families):
  a `||`-guarded body inside a loop whose body throws *out* of the loop and feeds a
  loop-carried accumulator. `find_gated_body`'s closure check required region-exit successors
  to be in `region_blocks`, but an out-of-loop throw isn't in `loop_blocks`; the multiplexer
  bailed and the diverge path dropped the body. Fixed by the region-exit rule.

**Deferred, with a finding that revises Decision 2.** The premise that irreducible "falls out
of the N-entry multiplexer at low marginal cost" assumes the general N-entry multiplexer
exists. It does not, and building it is **not** low-cost in the current architecture:

- Our structurizer is a **recursive walk** over an immutable `IRCode` CFG that *builds*
  structured ops directly. MLIR's multiplexer instead **mutates the CFG** — it inserts a
  single mux block, redirects the N entry edges into it (writing per-entry arg slices, a
  discriminator, and `undef` for the other entries), and emits a `cf.switch`; only *then* does
  the lifting run, now seeing single-entry regions. Our `emit_gated_branch!` is a *direct*
  realization of the 2-entry case (a boolean selector + one `scf.if`), not a CFG mutation.
- Reducible **acyclic** Julia CFGs never produce a >2-entry continuation — short-circuits
  (`a||b||c`, mixed `&&`/`||`) nest into 2-entry shapes at every level (verified empirically).
  So the 2-entry `find_gated_body` *is* the complete acyclic multiplexer; the only genuine
  N>2 / multi-entry need is the **irreducible loop** (D-mux).
- Therefore the clean way to retire `find_gated_body` *and* add irreducible support together
  is a **CFG-mutation pre-pass** (the MLIR architecture): insert mux blocks at every
  multi-entry continuation and multi-entry loop header, then run the existing walk with no
  multi-entry special cases. That is a substantial, architecture-level change — it should be
  done deliberately, not rushed, and is left for a follow-up with the maintainer in the loop.
  A narrower alternative is a dedicated `emit_irreducible_loop!` (loop-carried discriminator +
  dispatch, per `TODO.md`), but that adds a *second* multiplexer manifestation rather than
  unifying.

**Irreducible investigation (to de-risk the follow-up).** The `@goto` example in `TODO.md`
lowers to an SCC `{BB3, BB5, BB6, BB8}` with two entry blocks `BB3` (from `BB1`) and `BB6`
(from `BB2`); `Compiler`'s `CFGReachability`/`bb_in_irreducible_loop` (already imported)
flags exactly those four blocks. Each entry has its own header phi (`BB3`: `φ(#8,#1)`, `BB6`:
`φ(#2,#5)`); the entry mux carries a discriminator + the union of those phi operands, with
`undef` fill, and dispatches header → `BB3`/`BB6`. `TODO.md` is otherwise **stale**: its
"immediate fix: detect and reject" is already implemented (`check_irreducible`).

**Known unsupported shape (now loud, was silent).** Nested gated bodies inside a loop (e.g.
`for k; if a||k>1; if b||k>2; s+=k; end; end; end`) fail loudly via SSA validation; on the
#48 baseline they *silently miscompiled*. This needs the nested-multiplexer handling above.
