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
│ %2 = if %1 -> Nothing
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
    stmt(inst)       # underlying statement (Expr, ControlFlowOp, etc.)
    value_type(inst) # Julia type of the instruction result
end
```

#### `terminator(block::Block)` / `terminator!(block, term)`

Get or set the block's terminator (`ReturnNode`, `YieldOp`, `ContinueOp`, `BreakOp`, `ConditionOp`, or `nothing`).

#### `operands(term)` → `Vector{IRValue}`

Get the carried-value operands of a terminator. Provides uniform access regardless of terminator type (`.values` for `YieldOp`/`ContinueOp`/`BreakOp`, `.args` for `ConditionOp`).

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

### Block Mutation

All insertion functions auto-allocate fresh SSA indices.

#### `push!(block, stmt, typ)` / `pushfirst!(block, stmt, typ)` → `Inst`

Append or prepend an instruction.

#### `insert_before!(block, ref, stmt, typ)` / `insert_after!(block, ref, stmt, typ)` → `Inst`

Insert relative to an existing `Inst` or `SSAValue`.

#### `delete!(block, inst::Inst)`

Remove an instruction from a block.

#### `update_type!(block, inst, new_type)`

Change the type annotation of an existing instruction.

#### `new_block_arg!(block, typ)` → `BlockArg`

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

The structurization pipeline converts Julia's unstructured SSA IR (with `GotoNode` and
`GotoIfNot`) into nested control flow operations (`IfOp`, `ForOp`, `WhileOp`, `LoopOp`).

```
Julia IRCode (from code_ircode, includes CFG)
     │
     ▼ control_tree.jl
Control Tree (hierarchical regions)
     │
     ▼ structure.jl
Structured IR (nested Blocks with IfOp/ForOp/etc.)
```

### Control Tree Construction

`ControlTree()` pattern-matches on the CFG (from `ir.cfg.blocks`) to identify structured
regions. Back edges are detected using `Core.Compiler.construct_domtree()`.

| Region Type | Pattern |
|-------------|---------|
| `REGION_BLOCK` | Linear chain of blocks |
| `REGION_IF_THEN` | Conditional with one branch |
| `REGION_IF_THEN_ELSE` | Diamond pattern (two branches merge) |
| `REGION_PROPER` | Multi-exit acyclic region (short-circuit `\|\|`/`&&`) |
| `REGION_TERMINATION` | Branch where one or more paths terminate (early return) |
| `REGION_WHILE_LOOP` | Header with back edge from body |
| `REGION_FOR_LOOP` | While loop with detected counter pattern |
| `REGION_NATURAL_LOOP` | General cyclic region |

Matched regions are contracted into single nodes, and the process repeats until the entire
CFG reduces to a single control tree.

For-loop detection analyzes phi nodes in loop headers to find induction variables with
patterns like `===(iv, bound)` or `slt_int(iv, bound)`.

### Structured IR Generation

`control_tree_to_structured_ir()` converts the control tree into nested `Block` structures:

- **`IfOp`**: Condition + then/else blocks, results via `YieldOp`
- **`ForOp`**: Lower/upper/step bounds + body block with induction variable as `BlockArg`
- **`WhileOp`**: Before (condition) + after (body) regions
- **`LoopOp`**: General loop with `ContinueOp`/`BreakOp` terminators

Phi nodes become explicit `BlockArg` values (like MLIR block arguments).


## Acknowledgements

Most of this package is based on [Cédric Belmant](https://github.com/serenity4)'s
[SPIRV.jl](https://github.com/serenity4/SPIRV.jl) structurization code.
