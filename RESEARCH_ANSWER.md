# MLIR `CFGToSCF` — Exact Structural Definitions, vs. `IRStructurizer.jl` Heuristics

All line citations are to `mlir/lib/Transforms/Utils/CFGToSCF.cpp` and `mlir/include/mlir/Transforms/CFGToSCF.h` in the current `main` of `llvm/llvm-project` (doxygen snapshot labeled "MLIR 23.0.0git"). The pass was authored by Markus Böck and added in review D156889 ("[mlir][cf] Add ControlFlow to SCF lifting pass"); per his EuroLLVM 2024 talk "Lifting CFGs to Structured Control Flow in MLIR" (Vienna, Apr 10–11 2024) the stated design goals are: "No code duplication • Arbitrary control flow • Dialect agnostic • Upstream as driver and --lift-cf-to-scf • Paper extended to handle: Block arguments, Multiple Return-like operations." It implements Bahmann, Reissmann, Jahre, Meyer, "Perfect Reconstructability of Control Flow from Demand Dependence Graphs," ACM TACO 11(4), 2015 (DOI 10.1145/2693261), §4.1 (Loop Restructuring) and §4.2 (Branch Restructuring) — corroborated by the D156889 summary itself: "This patch therefore adds a transformation making it possible to lift arbitrary control flow graphs to structured control flow operations. The algorithm used is outlined in https://dl.acm.org/doi/…". Line numbers reflect that snapshot and may drift slightly.

## TL;DR

- Every one of the five suspected heuristic divergences is real: MLIR uses **edge-domination** (single-predecessor test), not block-domination, for branch membership (Q1); chooses the continuation by **exclusion + an edge multiplexer**, with **no block-index sort** anywhere (Q2); and uses **one `EdgeMultiplexer` construction** to avoid all node duplication and to serve multi-entry loops, multi-exit loops, and multi-predecessor merges uniformly (Q3, Q6).
- The core emits **only condition-at-latch do-while loops** (`createStructuredDoWhileLoopOp` → `scf.while`); it **never** emits `scf.for`/while-at-top. All counted/rotated loop recognition is strictly downstream (Q5). Reduce-form capture is a **single escape-analysis sweep** with undef-initialization for partially-escaping values and no per-use-kind special cases (Q4).
- MLIR output is **invariant under basic-block renumbering** — it depends only on CFG topology + dominance. Irreducible CFGs are **handled, not rejected**, by the same multiplexer parameterized by N entries (Q6). The Julia `H-throw`/`H-mux`/`H-dup`/`H-merge` heuristics should be replaced by direct ports of the MLIR predicates below.

## Key Findings

| Question | MLIR's exact rule | Citation | Heuristic verdict |
|---|---|---|---|
| Q1 membership | Blocks dominated by successor T **only if T's single predecessor is E** (edge-domination); else T is continuation | CFGToSCF.cpp:977–990 | H-split (dominated-by-T minus overlap) **diverges** |
| Q2 continuation | `find_singleton` over continuation edges (exclusion); multiplexer if not unique/not post-dom; return-like handled structurally | CFGToSCF.cpp:1054–1116 | H-merge sort-by-index **fragile**, eliminable |
| Q3 multiplexer | One block, per-entry arg ranges + discriminator, undef fill, `cf.switch` dispatch | CFGToSCF.cpp:207–387 | H-dup tail-duplication **unnecessary**; H-mux is same path |
| Q4 reduce form | Single "defined-in / used-out" sweep over all args+results; undef for partial escapes | CFGToSCF.cpp:637–795 | Confirmed; no per-use-kind cases |
| Q5 loop form | Core emits do-while (`scf.while`) only; for/while-top is downstream | CFGToSCF.cpp:872–875 | Post-pass design validated |
| Q6 determinism | Topology + dominance only; no index sort; irreducible via N-entry multiplexer | CFGToSCF.cpp:805–831, 1096–1098 | H-mux rejection unnecessary |

## Details

### Q1 — Branch region membership (vs. H-split)

**MLIR's exact predicate.** In `transformToStructuredCFBranches`, for each successor edge `E -> succ`, MLIR first tests (CFGToSCF.cpp:981):

```
if (succ->getSinglePredecessor() != regionEntry)
  continue;   // leave this successor's branch region EMPTY
```

Only when `succ`'s *single* predecessor is the conditional block `E` does it then collect, in dominator-tree DFS pre-order, every block dominated by `succ` (CFGToSCF.cpp:985–989):

```
DominanceInfoNode *node = dominanceInfo.getNode(succ);
for (DominanceInfoNode *curr : llvm::depth_first(node)) {
  blockList.push_back(curr->getBlock());
  notContinuation.insert(curr->getBlock());
}
```

This is exactly the "blocks solely reachable through the edge `E -> T`" criterion. The edge `E -> T` dominates `T` **iff** `T`'s only predecessor is `E` (since `E` already reaches `T`, the only way every path to `T` traverses *this specific edge* is if `T` has no other in-edge). When the edge does not dominate `T`, `T`'s branch region is empty and `T` falls into the continuation. The header comment states the same intent: the algorithm "identifies all blocks that are dominated by a specific control flow edge and the region where control flow continues" (CFGToSCF.cpp:92–95).

**Why H-split diverges.** H-split assigns "all blocks dominated by `T`" to the then-region and "all blocks dominated by `F`" to the else-region, then removes the overlap. It uses *block* domination, not *edge* domination, so it never applies the single-predecessor test. A merge block that happens to be the true-successor is dominated by itself and will be pulled into the then-region by H-split, whereas MLIR correctly treats it as the continuation.

**Minimal divergence CFG (Q1).**

```
        E            E: cond_br %c, ^T, ^F
       / \
      F   |          F: br ^T            (F's only successor is T)
       \ /
        T            T: br ^X            (the merge / reconvergence)
        |
        X            X: return
```

Edges: `E->T` (true), `E->F` (false), `F->T`, `T->X`.

- Dominance: `E` dominates everything; `T`'s immediate dominator is `E` (both in-edges, `E->T` and `F->T`, originate at or below `E`), but `T` has **two** predecessors (`E` and `F`).
- **MLIR:** `T->getSinglePredecessor() != E` ⇒ the true-branch region is **empty**; `F->getSinglePredecessor() == E` ⇒ else-region = `{F}`. Continuation = `T`. Result: `scf.if %c { } else { F }`, then `T`, `X` spliced after. `T` executes on both paths — correct.
- **H-split:** then = blocks dominated by `T` = `{T, X}`; else = blocks dominated by `F` = `{F}`; overlap empty. H-split places `T` (and `X`) **inside the then-region**, so they run only when `%c` is true — a miscompile of the reconvergence point.

This is the airtight Q1 regression test: a successor that is simultaneously a merge.

### Q2 — Continuation by exclusion (vs. H-merge)

**MLIR determines the continuation purely by exclusion.** After computing the branch regions (and filling `notContinuation` with `regionEntry` plus every branch-region block), MLIR gathers all edges leaving the branch regions whose target is *not* in `notContinuation` (CFGToSCF.cpp:1082–1088):

```
for (Edge edge : successorEdges(block)) {
  if (notContinuation.contains(edge.getSuccessor()))
    continue;
  continuationEdges.push_back(edge);
  noSuccessorHasContinuationEdge = false;
}
```

The continuation block is then the **single common successor** of those edges (CFGToSCF.cpp:1096–1098):

```
Block *continuation = llvm::find_singleton<Block>(
    continuationEdges, [](Edge edge, bool) { return edge.getSuccessor(); },
    /*AllowRepeats=*/true);
```

If that singleton does not exist (multiple distinct reconvergence targets) **or** the continuation does not post-dominate all branch regions, MLIR synthesizes one continuation block with an `EdgeMultiplexer` (CFGToSCF.cpp:1102–1107) and reprocesses. **There is no sort, no block-index tie-break, and no post-dominator-tree query to *pick* the continuation** — post-dominance enters only as a boolean classification (`continuationPostDominatesAllRegions`), never as an ordering key. This makes the choice layout-independent.

**The return/unreachable case — exactly where H-merge falls back to sort-by-index.** A return-like (region-exit) block has no successors; `isRegionExitBlock` is literally `block->getNumSuccessors() == 0` (CFGToSCF.cpp:940–942). When a branch region contains such a block, MLIR sets `continuationPostDominatesAllRegions = false` and folds that block's *predecessor* edges into `continuationEdges` (CFGToSCF.cpp:1069–1079) so the synthesized single-entry block also covers the return paths (case 3 in the header comment, CFGToSCF.cpp:1018–1053). If **no** branch region has any continuation edge — i.e., every region ends in a distinct return-like op — that is case 2: MLIR **keeps** the control-flow op and recurses into its successors (CFGToSCF.cpp:1092–1094). At no point does MLIR compute "the only post-dominator is the virtual exit, so sort candidates." (This non-total replacement is also why the pass is named "lift" rather than "convert": per the official MLIR Passes documentation, "This pass is prefixed with 'lift' instead of 'convert' as it is not always guaranteed to replace all ControlFlow ops. If a region contains only a single kind of return-like operation, all ControlFlow operations will be replaced successfully. Otherwise a single ControlFlow switch branching to one block per return-like operation kind remains.")

**Minimal divergence CFG (Q2).**

```
        E             E:  cond_br %c, ^T, ^F
       / \
      T   F           T:  br ^M
      |   |\
      |   | \         F:  cond_br %c2, ^M, ^R
      |   |  R        R:  return                 (dead-end, no continuation edge)
       \ /            
        M             M:  br ^X
        |
        X             X:  return
```

Edges: `E->T`, `E->F`, `T->M`, `F->M`, `F->R`, `M->X`.

- **Immediate post-dominator of `E`** is the virtual exit: from `F` you can reach `R` (which returns) without passing through `M`, so `M` does not post-dominate `E`.
- **H-merge:** no real post-dominator ⇒ fall back to "collect candidate reconvergence blocks, sort by basic-block index, take the first." The candidate set includes `M` and the virtual exit / `R`-region; the winner depends on whether `M`, `R`, or `X` was numbered lower. Renumber the blocks and the pick changes — fragile.
- **MLIR:** `T`-region = `{T}`, `F`-region = `{F, R}` (`F` dominates `R`). `R` is a region-exit block ⇒ `continuationPostDominatesAllRegions=false`, and `F` (its predecessor) is added to `continuationEdges`. The non-`notContinuation` successors are `T->M` and `F->M`, so `continuationEdges` resolves to the singleton `M`. MLIR picks `M` as the continuation **regardless of numbering**, builds a single-entry multiplexer covering the `R` path, and reprocesses. Deterministic and layout-independent.

### Q3 — The edge multiplexer (vs. H-dup and H-mux)

**Exact construction** (`EdgeMultiplexer::create`, CFGToSCF.cpp:225–261):

1. Allocate a new block `multiplexerBlock` and insert it after the first entry block (CFGToSCF.cpp:231–232).
2. For each **distinct** entry block, append *that block's* block arguments to the multiplexer block, recording the start offset in `blockArgMapping` (CFGToSCF.cpp:240–245). Duplicate entries share one argument range.
3. If there is more than one distinct successor, add **one** discriminator argument whose type is the switch-flag type (CFGToSCF.cpp:251–254).
4. Append any `extraArgs` (the latch uses this for the `shouldRepeat` flag) (CFGToSCF.cpp:256–257).

**Redirecting an incoming edge** (`redirectEdge`, CFGToSCF.cpp:271–316): the edge's original operands are written into the target entry block's argument slots (CFGToSCF.cpp:288–293); the discriminator slot is set to `getSwitchValue(index-of-this-successor)` (CFGToSCF.cpp:297–300); extra-arg slots are filled (CFGToSCF.cpp:304–306); and **every other entry block's argument slots are filled with `getUndefValue(type)`** (CFGToSCF.cpp:309–311). The edge's successor is then pointed at the multiplexer block (CFGToSCF.cpp:314–315).

**Dispatch** (`createSwitch`, CFGToSCF.cpp:323–358): one switch case per distinct entry block on the discriminator, each forwarding that block's slice of multiplexer arguments to the original successor; the last entry becomes the `default` case. The switch is materialized through `interface.createCFGSwitchOp`, i.e. a `cf.switch`; the flag constants come from `getCFGSwitchValue` (an `arith` constant). If there is only one entry, the discriminator is omitted and a dummy flag is used (CFGToSCF.cpp:345–347).

**Why this makes node duplication unnecessary.** A shared tail (merge or short-circuit join) is reached from several places. Rather than cloning it into each branch (H-dup), MLIR redirects **all** those incoming edges to a single multiplexer block and emits the shared tail exactly once as the multiplexer's dispatch target / continuation. The discriminator argument records which path was taken so that the tail's phi/block-argument values are resolved without copying code. The header comment makes the "emit once" guarantee explicit: "If there are multiple entry blocks into Region T, a single entry block is created using a multiplexer block" (CFGToSCF.cpp:108–110). "No code duplication" is the first stated design goal of the pass (Böck, EuroLLVM 2024).

**Minimal short-circuit CFG (Q3): `if (a || b) { body }`.**

```
        E              E:   cond_br %a, ^body, ^chk
       / \
      |   chk          chk: cond_br %b, ^body, ^merge
      |  /  \
      body   |         body: ... ; br ^merge
        \   /
        merge          merge: ...
```

Edges: `E->body` (a true), `E->chk` (a false), `chk->body` (b true), `chk->merge` (b false), `body->merge`.

- `body` has two predecessors (`E`, `chk`) ⇒ by Q1's rule its branch region is empty; `chk`'s region = `{chk}`.
- `continuationEdges` target two distinct blocks — `body` (from `E` and `chk`) and `merge` (from `chk`) — so `find_singleton` returns null ⇒ MLIR builds **one** multiplexer block `bbM` over edges `{E->body, chk->body, chk->merge}` with a discriminator selecting `body` vs `merge`. **`body` is emitted exactly once**, inside the structured region; the discriminator threads the "did we take the short-circuit?" decision.
- **H-dup** cannot place `body` in a single dominance-based region, so it clones `body` into the `a`-true arm and the `b`-true arm — two copies with fresh SSA names (code-size blowup, exactly what the slide deck's "No code duplication" design goal forbids).

**One mechanism, three roles (unifying view).** The identical `EdgeMultiplexer::create` call backs all three constructs:

- **Multi-entry (irreducible) loop:** `transformCyclesToSCFLoops` calls `createSingleEntryBlock` over the union of entry and back edges when `entryEdges.size() > 1` (CFGToSCF.cpp:821–831).
- **Multi-exit loop latch:** `createSingleExitingLatch` builds a multiplexer over back edges + exit edges with an extra `shouldRepeat` arg (CFGToSCF.cpp:566–573, 589–593).
- **Multi-predecessor merge / continuation:** `transformToStructuredCFBranches` calls `createSingleEntryBlock` for the continuation (CFGToSCF.cpp:1103–1106).

So `H-mux` (irreducible support) is **the same code path** as the fix for `H-dup`, parameterized only by the edge set and `extraArgs`. Future N-entry support is a generalization, not a new algorithm.

### Q4 — Reduce form (loop-carried value capture)

`transformToReduceLoop` (CFGToSCF.cpp:637–795) defines reduce form as: "(0) No values defined within the loop body are used outside the loop body. (1) The block arguments and successor operands of the exit block are equal to the block arguments of the loop header and the successor operands of the back edge" (CFGToSCF.cpp:639–643).

**Single escape-analysis sweep.** The pass iterates over every loop block and applies one `checkValue` closure to **all** block arguments and **all** op results uniformly (CFGToSCF.cpp:768–777):

```
if (loopBlock == latch)        llvm::for_each(latchBlockArgumentsPrior, checkValue);
else if (loopBlock == loopHeader) llvm::for_each(loopHeaderArgumentsPrior, checkValue);
else                           llvm::for_each(loopBlock->getArguments(), checkValue);
for (Operation &op : *loopBlock)
  llvm::for_each(op.getResults(), checkValue);
```

`checkValue` walks each use; if the use's owner block (climbing out of nested regions) is **not** in `loopBlocks`, the value escapes, and it creates one exit-block argument and one loop-header argument and rewrites the outside use (CFGToSCF.cpp:717–766). The criterion is purely "defined inside, used outside" — there are no per-use-kind branches. The comment notes requirement (0) "is shared with LCSSA form in LLVM" but is simpler here because the loop is already structured (CFGToSCF.cpp:650–653).

**Undef-initialization for partial escapes.** When a carried value does not dominate all latch predecessors (it escapes on only some paths), MLIR adds a latch argument and, for each latch predecessor that the value does not dominate, passes `getUndefValue` instead (CFGToSCF.cpp:742–756):

```
Value succOperand = value;
if (!loopBlockDominates(*iter))
  succOperand = getUndefValue(value.getType());
```

New loop-header arguments are likewise back-filled with undef on non-latch entry edges (CFGToSCF.cpp:780–792). This is precisely the "carry undef where the value isn't defined on that path" behavior. The undef value itself is produced by the interface (for `cf`→`scf`, `ub.poison`, as seen in the multi-entry example output).

### Q5 — Loop form layering (vs. the post-pass)

The core lifts every cycle through exactly one loop constructor, `createStructuredDoWhileLoopOp` (CFGToSCF.cpp:872–875):

```
FailureOr<Operation *> structuredLoopOp =
    interface.createStructuredDoWhileLoopOp(
        builder, oldTerminator, newLoopParentBlock->getArguments(),
        loopProperties->condition, iterationValues, std::move(loopBody));
```

whose documented contract is "Creates a structured control flow operation representing a do-while loop." The structured loop produced by `createSingleExitingLatch` is by construction condition-at-latch: the single latch block holds both the back edge and the exit edge, and branches on the `shouldRepeat` flag (CFGToSCF.cpp:540–547, 597–605). The concrete `cf`→`scf` implementation (`ControlFlowToSCFTransformation::createStructuredDoWhileLoopOp` in `mlir/lib/Conversion/ControlFlowToSCF/ControlFlowToSCF.cpp`) builds an `scf.while` — MLIR's generic while/do-while op, with the exit condition in the `before` region (`scf.condition`) and the body + back edge in the `after` region (`scf.yield`). **`scf.for` is never emitted by the core or by the interface.**

The published example output confirms a do-while shape even for a source `while` loop: `--lift-cf-to-scf` turns a head-controlled CFG loop into `scf.while { %c = ...; %r:2 = scf.if %c {...} else {...}; scf.condition(...) } do { scf.yield }` (Böck, EuroLLVM 2024 slides). This is corroborated by the LLVM Discourse thread "Lifting CF loops to SCF loops creates do-while, is there a way to turn it into regular while?" (discourse.llvm.org/t/…/88774), whose reporter observes that "lifting cf dialect loops into scf while loops was creating a do-while with an if op in the before region." Recognizing a counted `scf.for` or rotating to a condition-at-top `while` is done by **separate downstream transforms**: `ForToWhile.cpp` (the inverse direction), and the `scf.while`→`scf.for` uplift `upliftWhileToForLoop`, added in PR #76108 "[mlir][scf] Uplift `scf.while` to `scf.for`" by Ivan Butygin (GitHub @Hardcode84); the standalone-vs-canonicalization debate is captured in his Discourse RFC "`scf.while` → `scf.for` uplifting as canonicalization" (thread 78370): "there was some discussion about making it part of scf.while canonicalization instead of standalone transformation." This validates keeping while/for recognition as a strict post-pass over the generic loop op.

### Q6 — Determinism and irreducibility

**Invariance under renumbering.** The driver worklist starts at the region entry and recurses; cycles are found with `llvm::scc_begin` over the CFG (CFGToSCF.cpp:805) and branch regions are computed from `DominanceInfo`. The continuation is selected by `find_singleton` over an exclusion set (Q2), never by block index. Ordering enters only in places that do not affect the *classification* of blocks into regions:

- the DFS pre-order `llvm::depth_first` over a dominator subtree (CFGToSCF.cpp:986) only populates set-membership lists;
- `scc_begin` processes outermost cycles;
- `createSwitch` enumerates `blockArgMapping` in insertion order (deterministic given edge order, CFGToSCF.cpp:332).

There is no `sort` keyed on block index anywhere in the file. Consequently the output depends only on CFG topology + (post)dominance, not on the textual block order. (For contrast, MLIR's `Mem2Reg` explicitly relies on topological block order for determinism; `CFGToSCF` does not need to.)

**Irreducible CFGs are handled, not rejected.** The header states the algorithm works on "control flow graphs containing irreducible control flow" (CFGToSCF.cpp:19–20). A multi-entry cycle is converted to single-entry by the **same** `EdgeMultiplexer` used in Q3, via `createSingleEntryBlock` when `edges.entryEdges.size() > 1` (CFGToSCF.cpp:821–831); the multiplexer's discriminator dispatches N-way through `cf.switch`. The only hard preconditions (`checkTransformationPreconditions`, CFGToSCF.cpp:1239–1297) are: no unreachable (predecessor-less, non-entry) blocks; all terminators with successors implement `BranchOpInterface`; branch ops are side-effect-free; and no operation-produced successor operands. Irreducibility is **not** among them. The published `multi_entry_loop` example shows a two-entry irreducible loop lifted to an `scf.while` whose body is an `scf.index_switch` with one case per entry (Böck slides). Thus the N-entry entry multiplexer is the same construction as Q3, parameterized by N — `H-mux`'s outright rejection of irreducible CFGs is unnecessary, and supporting N entries is a generalization of the existing merge/short-circuit multiplexer rather than a new code path.

## Recommendations

1. **Replace H-split with the edge-domination predicate (Q1).** For each conditional successor `succ` of `E`, include `succ`'s dominated subtree in that arm **only if `succ` has `E` as its unique predecessor**; otherwise treat `succ` as continuation. Port the single-predecessor test (CFGToSCF.cpp:981) verbatim. Add the Q1 CFG (`E→{T,F}`, `F→T`, `T→X`) as a regression test asserting `T` lands in the continuation, not the then-region.
2. **Delete the sort-by-block-index fallback in H-merge (Q2).** Compute the continuation by exclusion (`notContinuation` set) and `find_singleton`; when the singleton is absent or a branch region contains a return-like/unreachable block, synthesize a single continuation via the multiplexer and reprocess. Port the case 1/2/3 classification (CFGToSCF.cpp:1054–1116). Add the Q2 CFG (`E→{T,F}`, `F→{M,R}`, `R: return`) as a renumbering-invariance test.
3. **Build the edge multiplexer and remove tail duplication (Q3/H-dup) and the irreducible-CFG rejection (H-mux) together.** Implement one `EdgeMultiplexer` (per-entry argument ranges + a discriminator block argument + undef fill + `switch`/compare-chain dispatch) and route (a) multi-predecessor merges, (b) multi-exit latches, and (c) multi-entry loop headers through it. Add the `if (a || b) { body }` CFG as a test asserting `body` appears exactly once.
4. **Keep reduce-form capture as one escape sweep (Q4).** Enumerate all block arguments and op results of loop blocks; promote any value with a use outside the loop to a header+exit block argument; pass undef on predecessor edges that the value does not dominate. Do not special-case use kinds.
5. **Keep while/for recognition strictly downstream (Q5).** Emit only the generic `LoopOp` (do-while) from the core; recognize `WhileOp`/`ForOp` in a separate post-pass over the generic loop op, mirroring MLIR's `ForToWhile`/`upliftWhileToForLoop` split.

**Benchmarks/thresholds that would change these recommendations.** If a target dialect cannot represent an N-way dispatch (no switch and no compare chain), the multiplexer degrades and tail duplication may be unavoidable for that dialect only. If profiling shows the discriminator/undef overhead dominates for hot short-circuits, a *targeted* duplication of tiny, side-effect-free tails could be reintroduced as an optimization layered *after* the multiplexer-based correctness pass — never as the primary mechanism.

## Contrast with `StructurizeCFG.cpp` (the model NOT to follow)

LLVM's `llvm/lib/Transforms/Scalar/StructurizeCFG.cpp` is a fundamentally different, predicate/flow-block approach and is worth contrasting to confirm `CFGToSCF` is the right model for `IRStructurizer.jl`. `StructurizeCFG` *linearizes* successors by inserting synthetic "Flow" blocks and a network of boolean PHI predicates: "The back edge of the 'Flow' block is always on the false side of the branch while the true side continues the general flow. So the loop condition consists of a network of PHI nodes where the true incoming values express breaks and the false values express continue states" (StructurizeCFG.cpp:274–277). It is built around `Predicates`, `Conditions`, `LoopPreds`, `LoopConds` maps and `buildCondition`/`gatherPredicates`/`insertConditions`, and it relies on `RegionInfo` + `UniformityInfo` because it targets execution-mask hardware. Two consequences matter for the Julia port: (a) it produces *predicated linear flow*, not nested structured regions with explicit yielded values, so it does not give you `IfOp`/`LoopOp` with region results; and (b) its node ordering (the `orderNodes`/`Order` vector) is a first-class part of the algorithm, the opposite of `CFGToSCF`'s renumbering-invariance. `CFGToSCF`'s region-and-multiplexer construction maps directly onto IRStructurizer's four-op target; `StructurizeCFG`'s predicate network does not.

## Caveats

- Line numbers are from the current `main` doxygen snapshot (labeled "MLIR 23.0.0git"); they drift over time. The function names, header ASCII diagrams, and structural predicates are stable since the pass landed (D156889) and are the durable anchors.
- The concrete `scf.while` emission lives in `mlir/lib/Conversion/ControlFlowToSCF/ControlFlowToSCF.cpp` (`ControlFlowToSCFTransformation`); exact line numbers for `createStructuredDoWhileLoopOp`'s body could not be pinned from the retrieved sources, but the do-while (`scf.while`, never `scf.for`) shape is confirmed by the interface contract ("Creates a structured control flow operation representing a do-while loop"), the SCF dialect semantics (condition in the `before` region), the published lift output, and the Discourse do-while thread.
- The Bahmann et al. section numbers (§4.1 Loop Restructuring, §4.2 Branch Restructuring) are corroborated by multiple secondary sources (the numba-scfg project, the authors' GPU companion paper "Efficient Control Flow Restructuring for GPUs") rather than read verbatim from the paywalled TACO PDF; the chapter appears as B2.4 in the author's NTNU thesis reprint. The paper's branch-restructuring text reads: "…H, multiple branch subgraphs B_k and a tail subgraph T … The branch and tail subgraphs are restructured to closed CFGs, resulting in branch subgraphs with exactly one entry arc from H and one exit arc to the restructured tail subgraph T*. The algorithm is then applied recursively to each branch and tail subgraph…" — the same head/branch/tail partition MLIR implements as branch regions + continuation.
- The three divergence CFGs are constructed to expose the heuristic gaps cleanly; before adopting them as regression tests, round-trip each through `mlir-opt --lift-cf-to-scf` to capture the exact structured output as the golden file.