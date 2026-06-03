# IRStructurizer

Convert Julia's unstructured SSA IR into structured control flow representation (SCF-style operations).

## Quick Start

```julia-repl
julia> using IRStructurizer

julia> f(x) = x > 0 ? x + 1 : x - 1

julia> code_structured(f, Tuple{Int})
1-element Vector{Pair{StructuredIRCode, DataType}}:
 StructuredIRCode(
│ %1 = intrinsic Base.slt_int(0, _2)::Bool
│ %7 = if %1 -> Nothing
│ ├ then:
│ │   %3 = intrinsic Base.add_int(_2, 1)::Int64
│ │   return %3
│ ├ else:
│ │   %5 = intrinsic Base.sub_int(_2, 1)::Int64
│ └   return %5
) => Int64

julia> sci, ret_type = code_structured(f, Tuple{Int}) |> only
```

## API

### `code_structured(f, argtypes; validate=true)`

Get structured IR for function `f` with argument types `argtypes`.

- `validate`: Throw `UnstructuredControlFlowError` if unstructured control flow remains

### `StructuredIRCode(ir::IRCode; structurize=true, validate=true)`

Construct structured IR from Julia's `IRCode` (obtained via `Base.code_ircode`).

- `structurize`: Convert unstructured control flow (GotoNode/GotoIfNot) into structured operations
- `validate`: Throw `UnstructuredControlFlowError` if unstructured control flow remains

### Inspection

#### `instructions(block::Block)` → `InstructionIterator`

Iterate over instructions in a block as `Inst` objects. Each `Inst` bundles an SSA index, statement, and type.

```julia
for inst in instructions(block)
    inst[:stmt]      # underlying statement (Expr, ControlFlowOp, etc.)
    inst[:type]      # Julia type of the instruction result (or value_type(inst))
    inst[:flag]      # IR_FLAG_* bitmask (see Compiler/src/optimize.jl)
    inst.block       # containing block
end
```

#### `terminator(block::Block)` / `terminator!(block, term)`

Get or set the block's terminator (`ReturnNode`, `YieldOp`, `ContinueOp`, `BreakOp`, `ConditionOp`, or `nothing`).

#### `operands(term)` → `Vector{IRValue}`

Get the carried-value operands of a terminator. Provides uniform access regardless of terminator type (`.values` for `YieldOp`/`ContinueOp`/`BreakOp`, `.args` for `ConditionOp`).

#### `operands(op::ControlFlowOp)` → `Vector{IRValue}`

Get the values flowing into a control flow operation from the parent scope:

- `IfOp` → `[condition]`
- `ForOp` → `[lower, upper, step, init_values...]`
- `WhileOp` → `copy(init_values)`
- `LoopOp` → `copy(init_values)`

#### `operands(block, inst)` → `Vector{Any}`

Extract data operands from an instruction's statement. Handles `Expr` (`:call`/`:invoke`/`:new`/`:splatnew`), `PiNode`, and `ControlFlowOp`. Returns `Any[]` for unknown types. Extensible via `operands(::Block, s::MyType)` for domain-specific IR nodes.

#### `arguments(block::Block)` → `Vector{BlockArg}`

Get the block arguments (loop-carried values, induction variables).

#### `blocks(op::ControlFlowOp)` → `Tuple`

Get the immediate sub-blocks of a control flow operation (non-recursive, one level only).

#### `parent(block::Block)` / `root(block::Block)`

Navigate the block tree. `parent` returns the containing block (or `StructuredIRCode` for the entry block). `root` walks up to the `StructuredIRCode`.

### Traversal

#### `walk(f, root; order=:preorder)`

Walk all instructions in the IR, calling `f(inst, block)` for each. The callback returns a control symbol:

- `:advance` — continue normally (default if callback returns `nothing`)
- `:skip` — don't recurse into this op's sub-blocks (preorder only)
- `:interrupt` — stop the walk immediately

Supports `:preorder` (default) and `:postorder` via the `order` keyword.

#### `eachblock(sci_or_block)` → `Vector{Block}`

Pre-order traversal of all blocks, recursing into nested control flow ops.

#### `findblock(sci::StructuredIRCode, inst::Inst)` → `Union{Block, Nothing}`

Find the block containing a given instruction.

#### `reachable_terminators(block::Block)` → `Vector{Terminator}`

Collect the block's own terminator plus all loop exits (`ContinueOp`/`BreakOp`) reachable through nested `IfOp`s. `YieldOp` and `ConditionOp` are captured by their enclosing `IfOp`/`WhileOp` and not propagated outward.

### Expression Inspection

#### `iscall(stmt_or_inst)` → `Bool`

Check whether a statement is a `:call` or `:invoke` expression.

#### `resolve_call(stmt_or_inst)` → `(resolved_func, operands)` or `nothing`

Extract the resolved function and operands from a call expression. Resolves `GlobalRef` to the bound value. Returns `nothing` for non-call statements or unresolvable functions.

#### `callee(stmt_or_inst)` → raw function reference

Get the raw function reference from a call expression without resolving `GlobalRef`.

#### `callargs(stmt_or_inst)` → `SubArray`

Get the operand arguments of a call expression (excludes the function reference).

### Definition Lookup

#### `def(root, val::SSAValue)` → `Instruction` or `nothing`

Find the instruction that defines an SSA value. The instruction's `block` field gives the containing block. Performs a linear scan — for repeated queries, use `defs(root)`.

#### `defs(root)` / `def(idx, val::SSAValue)`

Pre-built index for O(1) definition lookup. Analogous to `uses(block)` which returns a `UseIndex`.

```julia
idx = defs(sci)
inst = def(idx, SSAValue(3))
if inst !== nothing
    inst[:stmt]       # the statement
    inst.block        # the containing block
end
```

### Block Mutation

All insertion functions auto-allocate fresh SSA indices.

#### `push!(block, stmt, typ)` / `pushfirst!(block, stmt, typ)` → `Inst`

Append or prepend an instruction.

#### `insert_before!(block, ref, stmt, typ)` / `insert_after!(block, ref, stmt, typ)` → `Inst`

Insert relative to an existing `Inst` or `SSAValue`.

#### `move_before!(inst, target)` / `move_after!(inst, target)`

Move an instruction from its current block to before/after `target` in `target`'s block. The instruction retains its SSA index. Analogous to MLIR's `Operation::moveBefore`/`moveAfter`.

#### `delete!(block, inst::Inst)`

Remove an instruction from a block.

#### `empty!(block::Block)`

Remove all instructions from the block body, preserving args, terminator, and parent.

#### `val in block` / `val ∈ block` → `Bool`

Check if a value is defined in this block. Returns `true` for `SSAValue`s in the body and `BlockArgument`s in the args; `false` for everything else (constants, `Argument`s, etc.).

#### `is_defined_outside(val, block_or_loop_op)` → `Bool`

Check whether a value is defined outside a block (and all its descendants), or outside a loop operation's regions. The loop-op overloads handle values like `ForOp.iv_arg` that aren't in the body's block args. Analogous to MLIR's `LoopLikeOpInterface::isDefinedOutsideOfLoop`.

#### `block[ssa_idx]` → `Instruction` / `block[ssa_idx] = (...)`

Access or mutate the entry at an SSA index. `block[idx]` returns the `Instruction` handle (throws `KeyError` if absent — pair with `haskey(block, idx)`). `block[idx] = nt` accepts any NamedTuple subset of `(stmt, type, flag)`; fields not mentioned are preserved. So `block[idx] = (type=Float64,)` overwrites only the type, keeping `stmt` and `flag`.

#### `inst[:stmt]` / `inst[:type]` / `inst[:flag]` (Symbol-keyed access)

Read or write a single field of an instruction's live entry. Modeled on `Core.Compiler.Instruction` (`Compiler/src/ssair/ir.jl`). Reads and writes go through the block's storage, so `inst[:type] = T; inst[:type]` round-trips. `inst[:ssa_idx]` and `inst[:block]` are also exposed.

When swapping `:stmt` for one with a different opcode, the old `flag` bits describe the OLD op and may be stale for the new one. Pass `inst[:flag] = IR_FLAG_NULL` (or `block[idx] = (stmt=…, flag=IR_FLAG_NULL)` for an atomic write), mirroring LLVM's "fresh instruction, then opt-in `copyIRFlags`" pattern.

#### `new_block_arg!(block, type)` → `BlockArg`

Add a new `BlockArg` to a block.

### Use Tracking

#### `uses(block::Block)` → `UseIndex`

Build an index of all use sites in a block (recursively). The returned `UseIndex` supports `idx[val]` → `Vector{UseRef}` and `haskey(idx, val)`.

Keys can be `SSAValue`, `BlockArg`, `Argument`, `Inst`, or plain `Int` (treated as SSA index).

#### `uses(block::Block, val)` → `Vector{UseRef}`

Find all use sites of `val` in a block. Linear scan — for repeated queries, prefer `uses(block)`.

#### `replace_uses!(block, old, new_val)`

Replace all uses of `old` with `new_val` (recursively).

### Loop Carries

#### `carries(op)` → `LoopCarries`

Get a view over a `ForOp`/`LoopOp`/`WhileOp`'s carried values. Encapsulates the positional coupling between `init_values`, body `BlockArg`s, and terminator values.

Supports iteration, indexed access, `filter!`, `deleteat!`, and `push!`.

#### `CarryRef` accessors

Each element of a `LoopCarries` is a `CarryRef` with read/write access:

- `init_value(c)` / `init_value!(c, val)` — the value passed into the loop
- `body_arg(c)` — the `BlockArg` visible inside the loop body (`before` region for `WhileOp`)
- `after_arg(c)` — the `after`-region `BlockArg` (`WhileOp` only)
- `term_value(c, terminator)` / `term_value!(c, terminator, val)` — the value passed back at a `ContinueOp`, `BreakOp`, `YieldOp`, or `ConditionOp`

#### Bulk mutation

- `filter!(pred, carries)` → `Dict{Int,Int}` — keep carries where `pred(::CarryRef)` is true
- `deleteat!(carries, indices)` → `Dict{Int,Int}` — remove carries at given indices
- `push!(carries, init_val, body_arg_type)` → `CarryRef` — append a new carry

All three return (or produce) an old→new index mapping and maintain consistency across init values, block args, and all reachable terminators.


## Implementation

The structurizer turns Julia's unstructured SSA IR (`GotoNode`, `GotoIfNot`, `PhiNode`)
into nested control flow operations: `IfOp`, `ForOp`, `WhileOp`, and `LoopOp`. It uses the
mutate-then-lift approach of MLIR's CFGToSCF pass (Bahmann et al. 2015).

```
code_ircode → IRCode
     │  ingest                       (structurize/multiplex.jl)
     ▼
MCFG                                 explicit-edge CFG: block args + per-edge operands
     │  normalize_cf!                collapse multi-entry regions to single-entry
     ▼
MCFG  (single-entry, reducible)
     │  lift_mcfg → structurize      (structurize.jl, walk.jl, loops.jl)
     ▼
StructuredIRCode                     nested Blocks with IfOp/ForOp/WhileOp/LoopOp
     │  promote_loops!               (structurize/promote.jl)
     ▼
StructuredIRCode  (loops classified)
```

### The MCFG

Julia's `IRCode` is dense (an SSA value is its own position) and falls through from a
`GotoIfNot` to the next block on a true condition, so you cannot redirect an edge in place.
`ingest` reads it once into an `MCFG`. There, each block has a stable id, explicit block
arguments, and a terminator whose edges each carry one operand per target argument. Block
arguments and per-edge operands replace phi nodes, so the value a predecessor P passes to
block B's k-th argument is just the operand on the edge from P to B. Redirecting an edge
stays local.

### Normalization

The lift only handles single-entry, reducible regions, so `normalize_cf!` runs first and
rewrites everything else into that shape. Several situations send a block more than one
entry edge: irreducible loop headers, multi-exit loops, and short-circuit continuations
among them. Each is routed through a single edge multiplexer (`EdgeMux`), an inserted entry
block that picks the real target from a discriminator argument. The pass repeats to a
fixpoint, so a region reaches the lift only once it is single-entry.

### The lift

`structurize_region!` walks the normalized `MCFG` and emits structured ops. A natural loop
becomes a `LoopOp` whose body re-enters with `ContinueOp` and exits with `BreakOp`. A branch
whose arms reconverge becomes an `IfOp`, each arm a nested region, with merge values passed
out through `YieldOp`. Phi results become `BlockArgument`s, and the value each predecessor
feeds in reads off its outgoing edge.

### Loop promotion

The lift emits only `LoopOp`. The `promote_loops!` post-pass rewrites the ones it
recognizes: a loop driven by an integer induction variable with a constant step becomes a
`ForOp`, and a loop that tests its condition before the body becomes a `WhileOp`. The rest
stay `LoopOp`.

### Reverse direction

The reverse direction (`unstructurize.jl`) lowers a `StructuredIRCode` back to `IRCode`
through `IRCode(sci)`. It is there for the tests, which round-trip the structurizer against
Julia's own IR. cuTile consumes the `StructuredIRCode` directly.


## Acknowledgements

This package started from [Cédric Belmant](https://github.com/serenity4)'s
[SPIRV.jl](https://github.com/serenity4/SPIRV.jl) structurization code. The structurizer now
follows MLIR's CFGToSCF pass (Bahmann et al. 2015).
