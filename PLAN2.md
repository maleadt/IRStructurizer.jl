# PLAN2 — Close I4: the universal edge multiplexer (mutate-then-lift)

**Audience:** an engineer/agent picking up IRStructurizer.jl with **no prior conversation
context**. This is the implementation brief for the one remaining structural gap — a uniform
N-entry edge multiplexer — and the architecture change it implies. It assumes the companion
docs in this repo and references them rather than repeating them.

## 0. Read these first (in order)

- **`CLAUDE.md`** — repo overview, public API, how to run tests, the four target ops.
- **`GROUND_TRUTH.md`** — the **review oracle**: invariants I1–I8, the (A)–(E) litmus, and §3
  "Current state" (what's closed, what's open). *This is the standard your work is judged by.*
- **`RESEARCH_ANSWER.md`** — exact MLIR `CFGToSCF` predicates for branch/merge/reduce-form
  (Q1–Q6), with `CFGToSCF.cpp` line citations.
- **`RESEARCH_ANSWER_2.md`** — **the authority for this plan.** It answers, with citations,
  three questions: is CFGToSCF the right model (yes), edge-multiplexer vs node-splitting
  (multiplexer, always, for us), and mutate-then-lift vs analyze-and-build (mutate-then-lift).
  Its C1–C5 + Recommendations are the design spec. `RESEARCH_QUESTION_2.md` is the question.
- **`PLAN.md`** — the prior roadmap; its **"Implementation status (rework branch)"** section
  records what is already done (Phases 1, 3, 4.1–4.3, D-throw) and *why* this plan exists (the
  earlier "deferred" finding that the N-entry mux needs an architecture change — now resolved
  by RESEARCH_ANSWER_2 in favor of mutate-then-lift).
- **`TODO.md`** — **stale**; its "detect and reject" irreducible fix is already implemented.
  Its "full fix" sketch (disc-as-carried-value) is one realization; prefer the mux per below.
- **MLIR source (local):** `~/Julia/src/llvm-project/mlir/lib/Transforms/Utils/CFGToSCF.cpp`
  and `~/Julia/src/llvm-project/mlir/include/mlir/Transforms/CFGToSCF.h` (the header comment +
  ASCII diagrams are the canonical prose). **Read these** — you are porting this pass. Line
  numbers in the RESEARCH docs are from a different snapshot; `grep` the local copy for the
  function names (`EdgeMultiplexer`, `createSingleEntryBlock`, `createSingleExitingLatch`,
  `redirectEdge`, `createSwitch`, `transformCyclesToSCFLoops`, `transformToStructuredCFBranches`,
  `transformToReduceLoop`, `ReturnLikeExitCombiner`).
- **`mlir-opt`** at `/opt/homebrew/Cellar/llvm/22.1.6/bin/mlir-opt` — capture/refresh golden
  references with `--lift-cf-to-scf` (see `test/goldens/`).

**Run the tests:** `julia --project -e 'using Pkg; Pkg.test()'` (~18s once precompiled; **697
tests** as of this branch). Julia is **1.12** here. Do **not** `git push`; land local commits.

## 1. The decision (from RESEARCH_ANSWER_2.md)

1. **Keep CFGToSCF/Bahmann as the model.** It is the only algorithm that is both
   value-yielding-region-targeted (θ→`LoopOp`, γ→`IfOp`) and duplication-free (C1).
2. **One `EdgeMultiplexer` for all multi-entry/-predecessor situations** — multi-entry
   (irreducible) loop headers, multi-exit loop latches, multi-predecessor branch
   continuations. Never node-split (worst-case 2^(n−1), Carter–Ferrante–Thomborson) (C2, C3).
3. **Mutate-then-lift.** Physically insert mux/latch/dispatch blocks and redirect edges so the
   CFG is single-entry/single-exit *first*, then run a trivial lift that **never sees a
   multi-entry region**. This is the architecture that removes corner cases instead of
   accreting them; analyze-and-build "must handle multi-entry inline at every recursion,
   multiplying corner cases" (C4). The current pass is analyze-and-build — that is the change.

The end state closes invariant **I4** and empties the "Open" table in `GROUND_TRUTH.md` §3:
`find_gated_body` is deleted, irreducible CFGs are lifted (not rejected), nested gated bodies
work, and the lift only ever structurizes single-entry regions.

## 2. Where we are (so you don't redo it)

Already principled and **verified** (see `GROUND_TRUTH.md` §3 "Closed / aligned" and
`PLAN.md` status):

- **Merge by exclusion** — `find_branch_regions` (`src/structurize/loops.jl`) picks the merge
  as the `branch_continuation` singleton; no block-index `sort!` anywhere (I1, I3).
- **Edge-domination branch split** — single-predecessor gate (I3).
- **Region-exit rule** — `is_region_exit` = `numSuccessors==0` (return *or* throw), re-
  materialized in place, not dropped (I8). `src/structurize/walk.jl`.
- **Reduce form** — one escape sweep (`find_extra_exit_values`, `stmt_ssa_uses`) (I5).
- **Loop-form layering** — core emits only `LoopOp`; `WhileOp`/`ForOp` in `promote_loops!`
  (`src/structurize/promote.jl`); guarded by the `promote=false` test (I6).

The **one open gap (I4):** the multiplexer is realized only as a 2-entry short-circuit
pattern-matcher, `find_gated_body` + `emit_gated_branch!`, and irreducible CFGs are rejected
by `check_irreducible`. Symptoms this gap caused (now either fixed or failing-loud, but the
*root* is the missing uniform mux):
- A `||`-guarded body inside a loop that throws out of the loop and feeds a loop-carried
  accumulator **silently miscompiled** until a closure-check fix on this branch (see the
  corpus testset "D-dup: gated body with in-body region-exits…"). It was found by **fuzzing**.
- **Nested gated bodies inside a loop** (e.g. `for k; if a||k>1; if b||k>2; s+=k; end; end; end`)
  still fail — they now error loudly via SSA validation (on the #48 baseline they silently
  miscompiled). This is the canonical case the mux must fix; add it to the corpus once it works.

## 3. Orientation: the code

Entry point `src/structurize.jl` → `structurize(ir; promote=true)`:
1. `check_irreducible(ir)` (`src/structurize/cfg.jl`) — **throws** on multi-entry SCCs. *M2
   replaces this with normalization.*
2. `StructurizeCtx` — holds `domtree`, `postdomtree`, `loop_map` (natural loops via
   `compute_natural_loops`), SSA/arg counters, `types`, `ssa_remap`, `line_map`.
3. `structurize_region!` (`src/structurize/walk.jl`) — the recursive **lift** walk. Emits
   block stmts, dispatches terminators, lifts loops (`emit_loop!`) and branches
   (`emit_branch!`). A `LoopCtx` (now carrying `exit_dest`) makes the walk loop-aware.
4. `src/structurize/loops.jl` — `find_branch_regions`, `branch_continuation` (the exclusion
   analysis — **reuse this to find continuations to mux**), `find_gated_body` (the 2-entry
   special path — **delete in M3**), `emit_loop!`, loop-phi extraction, reduce-form.
5. `promote_loops!` (`src/structurize/promote.jl`) — post-pass `LoopOp`→`WhileOp`→`ForOp`.
   Untouched by this plan.
6. `src/unstructurize.jl` — the inverse (structured → flat `IRCode`). **`assemble_ircode`
   there is your model for emitting a dense `IRCode` from a block list** (CFG construction,
   SSA densification, debuginfo). M1 emit is the same shape of code, run on the *input* side.
7. `src/ir/` — output types, validation (`validate_scf`, `validate_ssa_defs`,
   `validate_ssa_uniqueness`, …), printing. **Validation is your safety net — keep it green;
   it is what turns a would-be silent miscompile into a loud failure.**

## 4. The crux difficulty (read before writing M1)

MLIR mutates because its IR is a mutable linked list of blocks. **Julia `IRCode` is dense and
fallthrough-sensitive**, which makes "mutate the CFG" mean "rebuild the IRCode":

- **Dense SSA:** a statement's SSA value *is* its position in `ir.stmts`. Inserting statements
  renumbers everything after. → Carry **stable ids** through mutation (original position for
  existing stmts, fresh ids for new ones) and remap stable→dense only at emit.
- **Fallthrough:** `GotoIfNot(cond, dest)` branches to `dest` on **false** and **falls through
  to the next block** on **true**. So block *order* is semantic. Redirecting a fallthrough
  edge, or inserting a block, can break it. → Either order blocks so every `GotoIfNot`'s true
  target is the next emitted block, or insert a **trampoline** (`GotoNode true_target`) as the
  next block (which then becomes a new predecessor — fix the target's phi edges accordingly).
  Note you may negate the condition to choose which target falls through.
- **Phi edges** reference predecessor **block indices**. On reorder/insert they must be
  remapped; when an edge is redirected through the mux, that phi's predecessor becomes the mux
  block, and the value it carried is threaded through the mux's argument union (this *is* the
  SSA-phi → block-argument unification).
- **Debuginfo:** `ir.debuginfo` (1.12) is positional. Carry per-stable-id `codeloc` and re-emit
  it; give synthetic mux stmts a nearby line. The structurizer rebuilds its own `line_map` from
  positions, so a faithful re-emit keeps `test/debuginfo.jl` green.
- **No native switch:** Julia IR has no switch terminator. The mux's N-way dispatch is a
  **compare chain** of `GotoIfNot` on the integer discriminator (`disc==0`, `disc==1`, …, last
  case = default). The lift then turns that chain into nested `IfOp`s. For **N=2** the chain is
  a single `GotoIfNot` → one `IfOp`, so 2-entry output matches today's `emit_gated_branch!`.

There is no shortcut around this IR plumbing if we follow mutate-then-lift; it is the bulk of
M1. Build it once, test it hard, reuse it for M2/M3.

## 5. The work, in milestones

Each milestone lands **green** (all 697 tests + new ones) and is independently committable.
Commit often. Hold every change to the `GROUND_TRUTH.md` litmus.

### M1 — CFG-mutation foundation + the `EdgeMultiplexer` (new file `src/structurize/multiplex.jl`)

Goal: an additive, **unused-until-M2** library that can rebuild an `IRCode` with mux blocks
inserted and edges redirected.

1. **Explicit-edge mutable CFG.** Define a block form that separates concerns and makes edges
   explicit (no fallthrough reliance), e.g.
   `MBlock { phis::Vector{(id, PhiNode)}, body::Vector{(id, stmt, type, codeloc)}, term }`
   where `term` is one of `Goto(target)`, `CondBr(cond, true_target, false_target)`,
   `Return(val)`, `Unreachable`, and targets are block indices.
   - `ingest(ir) -> (blocks, entry, next_id)`: per block, split leading phis / body /
     terminator. For `GotoIfNot(c,dest)`: `true_target` = the CFG successor that isn't `dest`;
     `false_target = dest`. Fallthrough block (no terminator) → `Goto(next)` or `Unreachable`
     if it dead-ends (a `Union{}` throw block). Keep stable ids = original positions.
   - `emit(blocks, entry, argtypes, sptypes, debuginfo) -> IRCode`: choose a block order that
     preserves `CondBr` fallthrough (greedy: follow `true_target`; trampoline when broken);
     two passes (assign dense positions to every id, then remap all `SSAValue` operands and
     phi block-edges); reconstruct terminators (`GotoNode`/`GotoIfNot`/`ReturnNode`); build the
     `CFG` and `DebugInfoStream`. **Mirror `assemble_ircode` in `src/unstructurize.jl`.**
   - **First test = round-trip identity:** for every corpus function, `emit(ingest(ir))`
     executed via `OpaqueClosure` (see `test/runtests.jl::execute`) equals `f(args…)`, with no
     mutation. Get this rock-solid before anything else.

2. **`EdgeMultiplexer`** (port `EdgeMultiplexer::create` / `redirectEdge` / `createSwitch` from
   `CFGToSCF.cpp`). Given a set of incoming edges and the distinct target ("entry") blocks they
   go to, plus optional `extraArgs`:
   - Create one mux block whose arguments are the **union** of the entries' phi
     inputs/block-args, recording each entry's offset range; append a **discriminator** arg only
     when there is >1 distinct entry; append `extraArgs` at the tail.
   - **Redirect** each incoming edge to the mux: write the edge's real operands into its
     target entry's slots, set the discriminator to that entry's index, **`undef`-fill every
     other entry's slots** (use the `Undef(T)` type already in `src/ir/types.jl`), set
     `extraArgs`.
   - **Dispatch** from the mux: a compare-chain on the discriminator, one case per entry (last
     = default), each forwarding that entry's slice to the original entry block.
   - **Centralize all undef/poison generation here** and assert the dominance condition (a real
     value is passed only on an edge where its def dominates the predecessor; else `undef`) so a
     mis-set fill **fails loudly** rather than miscompiling (RESEARCH_ANSWER_2 C5a, Rec. 4).
   - **Sort the entries deterministically** before building (RESEARCH_ANSWER_2 C5b / LLVM
     D74999 non-determinism bug; I1).
   - Unit-test: feed a hand-built multi-entry CFG (use `test/corpus.jl::build_ir`), mux it,
     assert the result is single-entry and round-trips.

**Exit:** `multiplex.jl` round-trips every corpus IR identically; the mux primitive produces a
valid single-entry IRCode on synthetic multi-entry inputs. Nothing else wired yet → 697 green.

### M2 — Irreducible entry mux (delete the `check_irreducible` throw)

Most separable application (irreducibility is a pure CFG property), and it validates M1.

1. Detect multi-entry SCCs and their entry blocks. `CFGReachability` /
   `bb_in_irreducible_loop` are already imported (`src/IRStructurizer.jl`); use them to flag
   irreducible blocks, then find the SCC's entry blocks (in-SCC blocks with a predecessor
   outside the SCC) and the edges into them (external entries **and** in-SCC back edges to a
   different entry).
2. Insert **one entry mux** per multi-entry SCC over (entry ∪ back) edges
   (`createSingleEntryBlock` when `entryEdges.size() > 1`, `CFGToSCF.cpp`). The mux becomes the
   single loop header → a natural, single-entry loop the existing `emit_loop!` lifts. Keep it a
   `LoopOp` (no While/For promotion — there is no single counting condition).
3. Replace `check_irreducible`'s `throw` with this normalization (run it in `structurize`
   before building `StructurizeCtx`, then build the ctx on the normalized IR so dominance is
   fresh). Keep a loud error only if normalization itself cannot apply.
4. **Tests:** the canonical `@goto` example (below) plus 1–2 synthetic N-entry irreducible CFGs
   via `build_ir`; assert each `@roundtrip`s. The example lowers to an SCC `{BB3,BB5,BB6,BB8}`
   with two entry blocks `BB3` (from `BB1`) and `BB6` (from `BB2`):
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
   Header phis to unify: `BB3: φ(#8,#1)`, `BB6: φ(#2,#5)`.

**Exit:** irreducible CFGs lift and round-trip; `check_irreducible`'s rejection is gone; 697 +
new tests green. (Watch-list row **D-mux** → closed.)

### M3 — Continuation mux → delete `find_gated_body` (closes I4)

Route every multi-predecessor branch continuation through the same mux so the lift sees a
single-entry continuation; then delete the 2-entry special path.

- **Reuse `branch_continuation`** (`loops.jl`) — it already computes the continuation entries
  by exclusion (loop-aware). A continuation with `length(entries) > 1` is exactly what must be
  muxed (`createSingleEntryBlock` for the continuation, `CFGToSCF.cpp`
  `transformToStructuredCFBranches`).
- After muxing, the continuation is single-entry: `find_branch_regions` returns a singleton
  merge and the **ordinary** `emit_branch!` path lifts it. **Delete `find_gated_body` and
  `emit_gated_branch!`**, and the `merge === nothing` multi-entry ambiguity in `emit_branch!`.
- **For N=2 the output must equal today's** (`if disc { body } { … }`, body emitted once) so
  the existing short-circuit structural tests stay green (e.g. `count_stmts(... :setfield!)==1`
  in `test/corpus.jl` and the `test/structurize.jl` "REGION_PROPER"/"short-circuit …" sets).

**Architecture decision to settle first (a short spike):** *where* does continuation-muxing
run?
- **(Recommended) Upfront-fixpoint normalization.** Add `normalize_cf(ir) -> ir'` that loops
  {recompute dominance/SCCs → find one multi-entry situation (irreducible header / multi-pred
  continuation / [M4] multi-exit latch) → mux it} until none remain, then `structurize` lifts
  `ir'`. Termination: each mux strictly reduces the count of multi-entry situations (the mux
  block is single-entry by construction). This keeps mutation and lifting **fully separate**
  (the cleanest mutate-then-lift) and lets the lift walk stay intact minus the deleted special
  cases. Continuations are identifiable upfront because `branch_continuation` needs only
  dominance + the arm regions, not the lifted form — but it **must** be back-edge-aware (pass
  loop context / skip edges where the successor dominates the source), which the existing
  `branch_continuation` already is.
- **(Reference) MLIR-interleaved.** MLIR lifts cycles first (collapsing each loop to one node),
  *then* lifts branches, muxing continuations as it recurses (`transformCyclesToSCFLoops` then
  `transformToStructuredCFBranches`, with dominance invalidated after each mutation). More
  faithful but requires restructuring our driver around a worklist. Fall back to this if the
  upfront fixpoint hits a case where a continuation is only well-defined after cycle lifting.

Validate the choice on the nested-gated-in-loop case and the AcceleratedKernels-shaped tests
before committing to it.

**Exit:** `find_gated_body`/`emit_gated_branch!` deleted; one branch-lift path handles
diamonds, short-circuits, N-way merges, and (via M2) irreducible entries; nested gated bodies
round-trip; **I4 holds**; `GROUND_TRUTH.md` §3 "Open" is empty except the minor M4 row.

### M4 — Multi-exit latch mux (optional cleanup, lower priority)

Route a loop's multiple exit edges through the same mux with a `shouldRepeat` `extraArg`
(`createSingleExitingLatch`, `CFGToSCF.cpp`): a conditional branch on `shouldRepeat` makes the
single back edge, a switch dispatches the exits. This collapses `find_loop_exit`'s
primary-exit preference heuristic (and the `Union{}` skip in `find_extra_exit_values`) into the
uniform mechanism. Current handling is correct (I8-safe); do this only to finish unifying I4.

## 6. Cross-cutting (from RESEARCH_ANSWER_2 C5 — bake in, don't bolt on)

- **Undef-fill correctness** lives in exactly one place (the mux `redirectEdge` equivalent),
  with a dominance assertion (C5a, Rec. 4). A second sweep fills new header args on non-latch
  entry edges — mirror `transformToReduceLoop`'s undef handling.
- **Determinism:** sort mux entries; never let block-index order leak into structure (I1, C5b).
- **Multiple return-like exits:** MLIR is named *lift* (not *convert*) because with several
  return-like op *kinds* it leaves a residual switch (`ReturnLikeExitCombiner`, C5d). **Our IR
  permits early `return`/`throw` as a region terminator**, so each becomes a region terminator
  rather than something funneled to one block — we **sidestep** the residual-switch machinery
  for the common case and need *less* than MLIR. Do **not** port `ReturnLikeExitCombiner` unless
  a concrete case demands it; rely on the existing region-exit rule (`is_region_exit`).

## 7. Testing strategy (non-negotiable)

- **Keep all 697 tests green at every commit** (I7/I8). `test/corpus.jl` is the tagged net;
  `test/runtests.jl::@roundtrip` and `execute` are the harness.
- **Round-trip identity** for M1 (`emit(ingest(ir))` executes == direct).
- **Fuzz multi-entry shapes** with exec-vs-direct comparison — *this is how the two latent
  silent miscompiles on this branch were found; a green corpus did not catch them.* Vary:
  `||`/`&&`/3-way guards, guards in loops with carried accumulators, nested guards, guards
  whose body throws/returns, irreducible `@goto`. Any "WRONG" (executes but mismatches) is a
  silent miscompile — the worst outcome; treat as a hard stop.
- **Structural assertions**, not just execution: body-emitted-once (count statements),
  merge identity, "no `find_gated_body`/`check_irreducible` left". Add a nested-gated-in-loop
  roundtrip + structural test once M3 lands.
- **Goldens:** refresh `test/goldens/` via `mlir-opt --lift-cf-to-scf` for any new divergence
  CFG; assert our output matches the *shape* (see `test/goldens/README.md` for the one
  legitimate divergence — we represent early return/throw directly where `scf` must linearize).
- **Renumbering invariance** (I1): the Q2 two-layout test in `test/corpus.jl` is the pattern;
  add one for an irreducible CFG built in two block orders → identical structure.

## 8. Definition of done

- One mechanism (`EdgeMultiplexer`) for every multi-entry/-predecessor situation; `find_gated_body`
  and the irreducible rejection both gone; the lift only structurizes single-entry regions (I4).
- No `sort!` on block indices, no shape-keyed `if` in the branch/loop lift (the litmus
  *inverts*: a future PR adding an `if <CFG shape>` to the lifter is a clear regression signal).
- `GROUND_TRUTH.md` §3 "Open" emptied (update it); D-mux and the special-case path marked
  closed; record that mutate-then-lift is the architecture so future changes don't reintroduce
  inline multi-entry handling.
- Corpus + fuzz + goldens green; no silent miscompiles.

## 9. Risks & sequencing notes

- **Biggest risk is M1** (the IRCode rebuild: fallthrough/trampolines, phi-edge fixup, dense
  renumbering, debuginfo). Land it behind the round-trip-identity test before any wiring.
- **M3 touches the hot path** and must reproduce N=2 output exactly — pin it with the existing
  short-circuit tests and the fuzz net; settle the upfront-vs-interleaved spike *before* the
  rewrite, not during.
- Order: **M1 → M2 → M3** (→ M4 optional). M2 is the de-risking milestone; if you must stop
  early, M1+M2 is still net-positive (irreducible support + the infra M3 needs).
- Branch: this work continues on `rework` (5 commits past the #48 baseline `9d84ca9`). The
  prior work — merge-by-exclusion, region-exit rule, corpus, I6 guard, two latent-miscompile
  fixes — is committed; build on it, don't redo it.

## 10. Implementation status (done)

**I4 is closed.** Mutate-then-lift is implemented in `src/structurize/multiplex.jl`
(`normalize_cf`), wired into `StructuredIRCode` before debug-info capture; the lift only ever
structurizes single-entry regions.

- **M1 — done.** `ingest`/`emit` (dense `IRCode` ↔ explicit-edge `MBlock` = block-args +
  per-edge operands; `emit` is non-mutating, preserves block order/flags/types/debuginfo, and
  inserts trampolines for `GotoIfNot` fallthrough + duplicate successors). `EdgeMultiplexer`
  (`create_mux!`/`redirect_edge!`/`dispatch!`/`single_entry_mux!`): union args + integer
  discriminator + undef-fill; dispatch is a `GotoIfNot` compare-chain (Julia has no switch);
  `absorb` reuses the entries' arg ids for the loop-header case; dead (all-undef) mux args are
  forwarded as `Undef`. Round-trip-identity + mux unit tests in `test/multiplex.jl`.
- **M2 — done.** Irreducible (multi-entry SCC) headers collapse to one entry mux (`absorb`) + a
  latch unifying the back edges → a plain reducible `LoopOp`. `check_irreducible` is a backstop.
  `@goto` corpus tests (N=2, N=3).
- **M3 — done.** Multi-predecessor continuations (short-circuits, N-way merges, nested gated
  bodies) route through the same mux upfront; **`find_gated_body`/`emit_gated_branch!` deleted**.
  `emit_branch!` has one path and asserts the continuation is single-entry. Nested-gated +
  generative-fuzz corpus tests.

**Fuzzing found and fixed silent miscompiles a green corpus missed** (and that the pre-PLAN2
baseline also had): the I8 region-exit rule was generalized from a region-exit *block* to a
region-exit *path* (`resolve_loop_exit!`/`emit_exit_path!`), and `promote_loops!` now keeps a
loop with a secondary `break` as a `LoopOp`. Vs baseline (extended fuzz, 200 generated fns):
silent miscompiles **0** (was 36), loud crashes ~416 (was 1192), structured 187/200 (was 160).

**Remaining (pre-existing, out of scope, loud not silent):**
- **M4 (the §3 minor row)** — the single-exiting latch that would replace `find_loop_exit`'s
  back-edge-adjacent heuristic. The heuristic is correct now (fuzzer-clean), so M4 is optional
  cleanup, not a correctness fix.
- **Nested-loop fragility** — a `break` in an *inner* nested loop fails to structurize (loud:
  "SSA used but not defined"), *identically on the pre-PLAN2 baseline*. This is the nested-loop
  extra-exit threading (`find_extra_exit_values`/`emit_loop!`), orthogonal to the branch mux —
  a separate loop-handling robustness effort. The generative fuzz net (`test/corpus.jl`) is the
  tool to drive it; it asserts no silent miscompile and exercises these shapes.
