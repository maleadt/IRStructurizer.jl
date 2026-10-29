# Exception handling

`StructuredIRCode(ir; exceptions=:structured)` (and `code_structured(...;
exceptions=:structured)`) lifts Julia's `EnterNode`-based try/catch to a structured
`TryOp`, and `IRCode(sci)` lowers it back. With the default `exceptions=:error`, an
`EnterNode` throws `UnstructuredControlFlowError`, so consumers that do not handle
`TryOp` keep rejecting try/catch. (`structurize=false` skips structurization and the
keyword with it: the flat IR keeps its `EnterNode`s.)

## Summary

- A try becomes a **`TryOp`** with two regions. The **body** is the protected code.
  The **handler** is the catch block, and it runs with the try's handler popped. The
  op sits at the `EnterNode`'s SSA index. Its results are the values of the single
  continuation, read with `getfield` as for `IfOp`.
- **`:leave` disappears.** Leaving the body pops the handler. Normal completion is a
  `YieldOp`. An exit from a nested region (an `IfOp` arm) is a new terminator,
  **`LeaveOp`**, which works like `BreakOp` but targets the innermost enclosing try
  body. This is the structured `:leave`, and it lowers to a Wasm `br` out of a
  `try_table`.
- **PhiC values become handler block arguments.** `TryOp.upsilons[k]` lists the
  `UpsilonNode` statements that feed argument `k`, and those statements stay where
  they are. A backend gives each argument a local, so an upsilon is a `local.set`
  and the handler entry reads it with `local.get`.
- **`:the_exception` and `:pop_exception` stay as statements.** They operate on
  Julia's exception stack, which is runtime state rather than control flow.
  `pop_exception %t` names the `TryOp` whose entry depth it restores.
- **Regions come from a handler-stack dataflow** (as in Julia's
  `compute_trycatch`). Normalization then gives every try a single continuation,
  and a loop that contains a try contains all of it. Afterwards
  `verify_try_structure` checks that every block still has one handler stack, so
  no mux joined paths with different handlers, and a throwing statement keeps the
  handler it unwinds to.

## 1. Julia's IR

| construct | meaning |
|---|---|
| `%e = EnterNode(catch_dest[, scope])` | Block terminator. It pushes a handler and falls through into the protected region, with an implicit edge to block `catch_dest` (`compute_basic_blocks` also gives the catch block a virtual predecessor `0`). `catch_dest == 0` is a scope-only enter: the optimizer proved the body nothrow but kept the scope (`Compiler/src/optimize.jl`). |
| `Expr(:leave, %e...)` | Pops one handler per non-`nothing` argument. It ends its block (`ir.jl`, `basic_blocks_starts`). A `return` out of nested trys pops several handlers at once. |
| `Expr(:pop_exception, %e)` | Restores the exception stack to its state at enter `%e`. It runs on every normal exit from a catch block, and can run after an enclosing try was already left (`leave %outer` comes before `pop_exception %inner`). |
| `Expr(:the_exception)` | Reads the current exception. |
| `%u = UpsilonNode(v)` / `PhiCNode(%u...)` | A value live into a catch block. Each assignment in the protected region (and one before the enter) feeds an upsilon. The catch block's `PhiCNode` reads whichever of its upsilons ran last. |

The handler stack is balanced: every block has one stack of active handlers on
entry. `Compiler.compute_trycatch` (`inferencestate.jl`) computes it and asserts
"unbalanced try/catch" otherwise. Everything below builds on that invariant.

```
 1 ─ %1 = enter #4                         %1 = try -> Tuple{Int64}
 2 ─ %2 = invoke g(_2)                     ├ body:
 └──      leave %1                         │   %2 = invoke g(_2)
 3 ─      return %2                        │   yield %2
 4 ┄      pop_exception %1                 ├ catch:
 └──      return -1                        │   pop_exception %1
                                           └   return -1
                                           %7 = getfield(%1, 1)
                                           return %7
```

## 2. The structured form

Implementation: `TryOp` and `LeaveOp` in `src/ir/types.jl`, the lowering in
`src/unstructurize.jl`.

### 2.1 `TryOp`

```julia
mutable struct TryOp <: ControlFlowOp
    body::Block                      # protected region
    handler::Union{Block, Nothing}   # catch region; `nothing` for a scope-only enter
    upsilons::Vector{Vector{Int}}    # per handler arg: SSA indices of its UpsilonNodes
    scope::IRValue                   # EnterNode scope (ScopedValues); undefined if none
end
```

- The op's SSA index is the `EnterNode`'s, so `pop_exception %t` keeps naming it.
  Its type is `Tuple{...}` of the continuation's live block arguments, extracted
  with `getfield` statements as for `IfOp`, and `Tuple{}` for a continuation without
  values. When the continuation is the merge of the enclosing region, the op's
  results are that merge's values, which the region then yields; its type is
  `Nothing` when that merge takes no values. It is also `Nothing` when there is no
  continuation, or when no path reaches it (the body and handler only throw or
  return). So a `Nothing` type does not by itself mean that the try diverges.
- **Body.** It ends in `YieldOp(values)` for normal completion, or in
  `ReturnNode()` when it ends in a throw. Nested regions leave it with `LeaveOp`.
  It never holds a `BreakOp`, `ContinueOp` or value `return`: those always come
  after the try's continuation (§3.3).
- **Handler.** It runs with this try's handler popped and the exception pushed. It
  ends in `YieldOp`, `ReturnNode(v)`, `ReturnNode()` (after `rethrow`), or
  `LeaveOp` when it sits in an outer try's body.
- `blocks(op)` is `(body, handler)`, or `(body,)` for a scope-only try. Generic
  walkers (`walk`, `eachblock`, `uses`, `replace_uses!`, `promote_loops!`) see
  both regions.

### 2.2 `LeaveOp` and region exits

`LeaveOp(values)` exits the innermost enclosing `TryOp` *body* and continues after
the op with `values` as its results. It can cross `IfOp` arms and the handler of an
inner `TryOp` (whose handler is already popped). It never crosses a loop or another
try body. `validate_terminators` checks this. It also checks that the body and
handler yields and every `LeaveOp` that exits the body carry the op's results
(arity and types), that no value `return` sits inside a body, and that each listed
upsilon is an `UpsilonNode`.

| exit | structured form | Julia IR (unstructurize) | Wasm |
|---|---|---|---|
| body completes | `yield v` in the body | `leave %t; goto merge` | `br $cont` |
| exit from a nested arm | `leave v` | `leave %t; goto merge` | `br $cont` (deeper label) |
| handler completes | `yield v` in the handler | `goto merge` | fall through / `br $cont` |
| `return` / `break` / `continue` out of a try | `yield` a discriminator; the return or loop edge follows the op | `leave`, then the original edge | `br $cont`, then `return`/`br` |
| throw inside the body | the throwing call, then `return` (unreachable) | unchanged | unchanged (caught by `try_table`) |

`break` and `continue` out of a try, and `return` out of its body, are not
terminators inside it. Normalization routes every exit of the try to one
continuation (§3.2), and the `IfOp` dispatch after the `TryOp` performs the
original transfer. (A handler may still end in a value `return` when no outer try
is active, §3.3.) This matches
how the package already gives loops a single exit, and keeps `TryOp` opaque to
loop promotion.

Example (`try; if x > 0; if x > 5; return 3x; end; y = g(x) else y = h(x) end; y + 1
catch; -7 end`):

```
%1 = try -> Tuple{Int64, Int64, Int64}
├ body:
│   %24 = if (0 < x) -> Tuple{Int64}
│   ├ then:
│   │   %22 = if (5 < x) -> Tuple{Int64}
│   │   ├ then:  %6 = mul_int(x, 3); leave 0, %6, undef      # exits the try
│   │   ├ else:  %9 = g(x); yield %9
│   │   yield getfield(%22, 1)
│   ├ else:  %11 = h(x); yield %11
│   %13 = add_int(getfield(%24, 1), 1)
│   yield 1, undef, %13
├ catch:
│   pop_exception %1
└   return -7
if getfield(%1, 1) === 0 → return getfield(%1, 2) else → return getfield(%1, 3)
```

### 2.3 Values into the handler

Each `PhiCNode` of the catch block becomes a handler block argument, and
`upsilons[k]` lists the `UpsilonNode` statements that feed it. Those statements
stay in place, in the body or just before the op, and are ordinary uses of their
operand (`walk_uses!`, validation and substitution all treat them so). This keeps
the handler SSA-clean: no reference into the body. It also tells a backend exactly
what to do:

- each handler argument `k` is a local `$u_k`;
- `UpsilonNode(v)` listed for argument `k` becomes `local.set $u_k v`. The reverse
  map, from upsilon to `(TryOp, k)`, comes from one walk over the `TryOp`s;
- handler entry reads `local.get $u_k`.

This is also how Julia's LLVM codegen implements upsilon/phic (an alloca per
PhiC), and what Liftoff, Graal and Cranelift do with locals or spills.

### 2.4 The exception stack

`Expr(:the_exception)` and `Expr(:pop_exception, %t)` stay as statements. Their
operand is the exception stack, which is also read by `rethrow()` and
`current_exceptions()`, runtime calls the structurizer cannot see. So the
exception is not made a handler argument. A backend models the stack directly:
push on handler entry, save the depth at each `TryOp` that a `pop_exception`
names, and restore it at `pop_exception %t`.

`pop_exception %t` is an ordinary use of `%t` for SSA scoping: it sits in the
handler of `TryOp %t` (or of a try nested in it), or after `%t` in a region that
`%t` dominates, so `%t`'s enter dominates it in lowered IR. Julia emits
`leave %outer` *before* `pop_exception %inner` when a catch returns out of an
enclosing try. Left there, the pop would sit after the outer `TryOp`, outside the
inner one, and after a loop around both if the return leaves one.
`hoist_pops_over_leaves!` moves the pops that open a block reached only through
`:leave`s to before those leaves, which is equivalent (a leave pops the handler
stack, a pop restores the exception stack), and puts the pop back in the inner
catch. A pop that leaves several catches at once (a `break` from a catch nested in
another catch pops straight to the outer state) is split by
`split_pops_across_catches!` into one pop per catch, so the exits of a handler all
hold the same exception state. The opposite order of pop and leave also occurs:
a `continue` out of a try nested in a catch pops the catch's exception and then
leaves the nested try. The nested try's continuation would then join an exit
whose exception is popped with its handler's exit, which still holds it, and the
outer handler region would have no end. `sink_pops_below_leaves!` moves such a
pop, and each pop the split produced, after the leaves that follow it, back to the
depth of its catch. These rewrites apply where their preconditions hold: a split
only where the enters of the catches involved dominate the block, a sink only
along a leave chain no other path shares, so a pop before a shared chain stays
one handler deeper than its catch. `verify_try_structure` then checks that every
pop runs where the TryOp it names is in scope (after the enter, outside the try's
body, and within the handlers active at the enter), and rejects the try otherwise.

### 2.5 Scoped values

`EnterNode(dest, scope)` (from `@with`) becomes a `TryOp` with `scope` set.
`EnterNode(0, scope)` becomes a `TryOp` with `handler === nothing`: entering sets
the scope and leaving restores it.

### 2.6 Lowering to Wasm (exnref)

```wat
;; %t = try -> (T...)   body / handler(%a_1..%a_n) / upsilons
block $cont (result T...)
  block $h (result (ref $jl_exn) exnref)        ;; one tag for Julia objects
    try_table (catch_ref $jl_tag $h)            ;; (+ catch_all_ref for foreign throws)
      ;; body; UpsilonNode(v) feeding a_k:  local.set $u_k v
      ;; yield v / leave v:                 br $cont v
    end
    unreachable                                 ;; body never falls through
  end
  ;; handler: push the exception on the Julia exception stack, keep the exnref
  ;; for rethrow (throw_ref), %a_k = local.get $u_k
  ;; yield v: falls through to $cont; return v: return; rethrow(): throw_ref
end
;; getfield(%t, i) are the block results
```

The handler is outside the `try_table` but inside `$cont`, which is the Julia
semantics: the handler runs with the try's handler popped. Since `LeaveOp` never
crosses a loop, every `br` it becomes is a forward branch to an enclosing block.

## 3. Recovering the regions

Implementation: `src/structurize/exceptions.jl`, plus small hooks in ingest,
normalize and the walk.

### 3.1 Handler stacks and the two regions

`ingest` turns `EnterNode` into an `MEnter` terminator: a body edge, the catch block
id, and the scope. It then makes every `:leave` a block of its own that pops one
handler (`split_leaves!`, innermost first, naming the enter it pops).
`handler_stacks` is the forward dataflow over `MEnter` pushes and `:leave` pops,
and it rejects unbalanced input. For a try entered at block B with stack σ:

- **R (body)**: blocks whose entry stack contains the try. Every edge out of R
  starts at a leave block and lands on a block with stack σ.
- **C (handler)**: blocks dominated by the catch block whose stack extends σ and
  that run before the catch's `pop_exception`, minus leave blocks that pop a
  handler in σ. A block runs before the pop when its exception state (the second
  component of `compute_trycatch`, `exception_states`) is this catch's, or that of
  a catch nested in it, or when it lies inside a try entered within the catch. The
  last case covers an exit out of such a try: Julia pops the catch's exception
  before it leaves the try, so the leave block runs after the pop but is still in
  the handler. The leave blocks of σ belong to the enclosing body: a handler
  that exits an outer try first reaches its leave block, which is then a
  continuation of *this* try. An empty block that only forwards one edge of a
  handler branch to that branch's other target also runs after the pop, but is
  part of C (`is_handler_forward`). `split_duplicate_edges!` makes such blocks
  before the lift, when a branch has both of its edges to the continuation, and C
  without them would have two exits.

  Dominance alone is not enough when the body cannot complete normally (it always
  throws, or loops forever as in `Base.wait_forever`). The catch block then
  dominates all the code after the handler, including each continuation that
  normalization builds. The handler would absorb every mux built for its exits,
  and normalization would never converge.

Because stacks are balanced, the bodies of different trys nest: an inner try's R
lies inside the outer R (or C), and so does a natural loop with its header in R.
The lift also needs each inner try's R ∪ C inside the region that contains its
enter, and raises an internal error when it is not. What remains is try-vs-loop
and try-vs-branch interaction, handled below.

### 3.2 Normalization (`normalize_one_try!`, first in the `normalize_cf!` fixpoint)

1. **Single continuation.** If the edges out of R ∪ C reach more than one block, or
   reach a loop header, route them through one `EdgeMux` K. The dispatch to the
   original targets (the return block, the loop latch, the after-try code) runs
   after the `TryOp`, outside every handler of the try. All these edges hold
   stack σ, so the mux is valid.
2. **Reduce form.** A value defined in R ∪ C and read in a block K dominates becomes
   a new block argument of K, and those reads are rewritten (`reduce_try!`). This
   is the try analogue of `reduce_loop!`. Afterwards nothing escapes the `TryOp`
   except through its results.

A later mux, whether a latch, continuation or pre-header, joins edges into blocks
of one handler stack. If one ever joined two stacks, its block would have both,
which `verify_try_structure` (through `handler_stacks`) rejects: it checks the
invariants after the fixpoint and throws `UnstructuredControlFlowError` instead of
lifting a shape it cannot represent.

### 3.3 Loops

- **Loop inside a try** needs no special handling. Its blocks lie in R, its exits
  stay in R, and its own latch is in R.
- **Try inside a loop.** `natural_loops_m` grows every loop that contains B by all
  of R ∪ C (`extend_loops_over_trys!`). Otherwise two things go wrong. A throwing
  dead end in R cannot reach the back edge, so it is not in the natural loop, and
  the latch would route it out of the loop, out of the try, past the handler. And
  a handler that leaves the loop would make the exceptional edge itself a loop exit
  that the latch would redirect. With the try inside, the loop's exits leave from
  the try's continuation K, which is in the loop and holds no handler of the try.
- **`break`/`continue`/`return` out of a try** go to K (§3.2 rule 1), and the
  post-try dispatch performs them. `LeaveOp` therefore never crosses a loop, and
  `promote_loops!` is unaffected: there are no loop exits inside a `TryOp`.
- A value `return` inside a handler stays where it is when no outer try is active,
  even inside a loop. `return` is a structured function exit. This differs from
  non-EH code, where a return in a loop is routed through the latch.

### 3.4 Branches inside a try

A branch in R may have one arm leave the try while its other arm continues in R.
That edge is not a continuation edge of the branch: the edge changes the handler
stack, so muxing it with an in-region edge would be wrong. `branch_continuation`
skips any edge into a block with a shallower handler stack than the branch (the
`depth` keyword), the same way it skips loop exits, in both normalization and the
lift. In the lift, `resolve_try_exit!` turns that edge into a `LeaveOp` carrying
the edge's operands into K. This also covers a throwing merge next to an exit,
which a funnel-style "try latch" could not: dead ends never reach the latch.

A branch in C can have one arm that pops the catch's exception and leaves the
handler while its other arm runs on in the catch and pops later (in a loop in a
catch with a `finally`, a `return` pops before the finally code runs, a `break`
after the loop). The mux for its continuation would join a path that holds the
exception with one that does not, and one of them would fall out of C. So
`continuation_mux!` moves the pops that only some of the edges ran to after the
mux, onto the dispatch edge to their target (`take_pops_before_mux!`), and the mux
stays in the catch.

### 3.5 Nesting corner cases

- **Multi-handler `:leave`** (`return` out of nested trys) is split into one
  leave block per handler, so each region boundary is a single edge.
- **A handler that leaves an outer try** (`catch; return ... end` inside another
  try): the outer leave block is excluded from C (§3.1). It becomes the inner
  try's continuation, and the outer exit happens after the inner `TryOp`, as a
  `LeaveOp` or `YieldOp` of the outer body. The trailing `pop_exception %inner` is
  moved before the outer leave (§2.4).
- **finally**: Julia lowering duplicates the finally code onto the normal path and
  the exceptional path (`catch; <finally>; rethrow()`). When the try has several
  exits it dispatches on a selector after a shared copy. Both are ordinary CFG to
  the structurizer, giving a handler that ends in `rethrow` (`ReturnNode()`) and a
  multi-exit continuation.
- **A body that cannot complete normally.** Every exit of the try is a handler
  exit, and the code after the handler is a continuation like any other (§3.1),
  even though the catch block dominates it.
- **Catch block reached by ordinary control flow** never comes out of Julia
  lowering. It is rejected.
- **Variables undefined on the catch path.** A variable never assigned before a
  throw gets a `Union{}`-typed `PhiCNode`, and phis carry it around merges and
  loops. Julia reads it only behind `throw_undef_if_not`. `undef_bottom_values!`
  turns every edge operand that carries such a value into `Undef`, and an upsilon
  of one into an undefined upsilon. The `Union{}` block arguments that nothing
  reads then are dropped, since the lift keeps every merge argument as a result. So
  the lift never builds a `Union{}` loop carry or result.

### 3.6 No unwind-destination mismatch

LLVM's mismatches come from placing try markers over a *linear layout*: code that
lands between the markers is protected whether or not it should be. Here regions
are the exact sets of blocks with the handler active, and the lift never moves a
statement out of its block. The only code normalization adds is mux dispatch
(`===` comparisons and gotos), which cannot throw. Two conditions remain, and the
dataflow guarantees them:

1. A block is never placed in a region with a different handler.
2. No mux joins edges with different handler stacks.

`verify_try_structure` checks the result, not the passes, and does not compare it
with the input IR: on the final MCFG every block still has one handler stack (a mux
that joined two stacks would break that), each catch block is reached only by its
exceptional edge, each try has one continuation that is not a loop header, and
every `pop_exception` runs where the TryOp it names is in scope. A
*catch-unwind* mismatch (an exception the handler does not catch) cannot occur
either. A Julia `catch` catches everything, and type filtering is ordinary code in
the handler followed by `rethrow`.

## 4. Alternatives considered

- **Handler as a branch target** (exnref-style `TryOp(body)` with an exceptional
  exit, the handler structured by the ordinary IfOp/mux machinery after it). Many
  compilers lower try this way (TeaVM, Graal, dart2wasm, LLVM). It removes
  handler-vs-outer-try nesting (§3.5) for free, but every try then yields a
  "caught" discriminator and the handler becomes an `IfOp` arm dispatched after it.
  That is noisier for the common `try … catch … end`, and it hides the handler's
  extent from consumers that want to drop it. The region form still lowers to the
  branch-target Wasm form directly (§2.6). If needed, it can be produced from a
  `TryOp` by moving the handler after the op.
- **A "try latch" instead of `LeaveOp`.** Funnel every exit of R through one block
  inside R, as the loop latch does, and keep only `YieldOp`. This needs no new
  terminator, but it fails when a throwing merge sits next to an exit: dead ends
  never reach the funnel. It also adds a discriminator for every early `return`
  inside a branch. `LeaveOp` matches ILSpy's `Leave` and Wasm's `br`.
- **Keep `PhiCNode` statements in the handler.** That is faithful to Julia, but the
  handler would reference body SSA values outside its scope. Block arguments plus
  `upsilons` say the same thing and keep the regions SSA-clean.
- **Explicit `:leave` statements inside regions.** Exits are already structural,
  and an explicit leave would let a body pop its handler midway, which no
  structured target can express.

## 5. Limitations

- The analyses reject what they cannot represent instead of lifting it:
  unbalanced handler stacks, a catch block also reached by ordinary control flow,
  a try left with more than one continuation, and a `pop_exception` outside the
  scope of the TryOp it names throw `UnstructuredControlFlowError`, as does a
  normalization that does not converge.
- The try analyses are recomputed on every normalization step. Code without a try
  does none of this work (`MCFG.has_eh`).
