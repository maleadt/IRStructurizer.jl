#=============================================================================
 Expression inspection
=============================================================================#

"""
    resolve_call(block::Block, stmt) -> (resolved_func, operands) or nothing
    resolve_call(block::Block, inst::Instruction) -> (resolved_func, operands) or nothing

Extract the resolved function and operands from a `:call` or `:invoke` Expr.
For `:call`, `stmt.args[1]` is the function reference and args 2+ are operands.
For `:invoke`, `stmt.args[2]` is the function reference and args 3+ are operands.

The callee is resolved via its inferred type using `singleton_type`, the same
mechanism Julia's compiler uses during inlining. This handles GlobalRef, literal
values, and SSAValue callees whose type is a singleton function type.

Returns `nothing` if `stmt` is not a call expression or the function cannot be resolved.
"""
function resolve_call(block::Block, @nospecialize(stmt))
    stmt isa Expr || return nothing
    if stmt.head === :call
        func_ref = stmt.args[1]
        operands = @view stmt.args[2:end]
    elseif stmt.head === :invoke
        func_ref = stmt.args[2]
        operands = @view stmt.args[3:end]
    else
        return nothing
    end
    resolved = resolve_callee(block, func_ref)
    resolved === nothing && return nothing
    return (resolved, operands)
end

resolve_call(block::Block, inst::Instruction) = resolve_call(block, inst[:stmt])

"""
    resolve_callee(block::Block, ref) -> resolved_func or nothing

Resolve a callee reference to a concrete function value. Uses `singleton_type`
on the inferred type (mirroring Julia's compiler) for symbolic refs (SSAValue,
Argument, BlockArgument, SlotNumber). Falls back to evaluating GlobalRef and
literal values directly, which is necessary for non-singleton types like
`Core.IntrinsicFunction` where all intrinsics share one type and
`singleton_type` returns `nothing`. Julia's inliner sometimes substitutes a
`GlobalRef(Core.Intrinsics, :sub_float)` callee with the literal
`IntrinsicFunction` value (e.g. when inlining cross-module wrappers like
`BFloat16s.:-`), so non-symbolic refs are returned as-is.
"""
function resolve_callee(block::Block, @nospecialize(ref))
    if ref isa SSAValue || ref isa Argument || ref isa BlockArgument || ref isa SlotNumber
        T = value_type(block, ref)
        T === nothing && return nothing
        return CC.singleton_type(T)
    end
    # GlobalRefs in optimized IR are guaranteed valid: inference rejects undefined bindings.
    ref isa GlobalRef && return getfield(ref.mod, ref.name)
    ref isa QuoteNode && return ref.value
    # Literal callable embedded directly as args[1] (e.g. an IntrinsicFunction
    # value substituted by Julia's inliner): the ref *is* the function.
    return ref
end

"""
    iscall(stmt) -> Bool

Check whether a statement is a `:call` or `:invoke` expression.
"""
iscall(@nospecialize(stmt)) = stmt isa Expr && (stmt.head === :call || stmt.head === :invoke)

"""
    iscall(inst::Instruction) -> Bool

Convenience overload: checks the underlying statement.
"""
iscall(inst::Instruction) = iscall(inst[:stmt])

"""
    callee(stmt::Expr) -> Any

Get the raw function reference from a `:call` or `:invoke` expression.
For `:call`, returns `stmt.args[1]`. For `:invoke`, returns `stmt.args[2]`.
Does NOT resolve GlobalRef; use `resolve_call` for that.
"""
function callee(stmt::Expr)
    if stmt.head === :call
        return stmt.args[1]
    elseif stmt.head === :invoke
        return stmt.args[2]
    end
    throw(ArgumentError("callee() requires a :call or :invoke Expr, got :$(stmt.head)"))
end

"""
    callee(inst::Instruction) -> Any

Convenience overload: extracts callee from the underlying statement.
"""
callee(inst::Instruction) = callee(inst[:stmt]::Expr)

"""
    callargs(stmt::Expr) -> SubArray

Get the operand arguments of a `:call` or `:invoke` expression (excludes function ref).
Returns a view into `stmt.args`.
"""
function callargs(stmt::Expr)
    if stmt.head === :call
        return @view stmt.args[2:end]
    elseif stmt.head === :invoke
        return @view stmt.args[3:end]
    end
    throw(ArgumentError("callargs() requires a :call or :invoke Expr, got :$(stmt.head)"))
end

"""
    callargs(inst::Instruction) -> SubArray

Convenience overload: extracts call arguments from the underlying statement.
"""
callargs(inst::Instruction) = callargs(inst[:stmt]::Expr)


#=============================================================================
 Instruction operands
=============================================================================#

"""
    operands(block::Block, inst::Instruction) -> Vector{Any}
    operands(block::Block, stmt) -> Vector{Any}

Extract data operands from an instruction's statement, the values the
instruction consumes. Handles `PiNode` and `ControlFlowOp` types natively.
Returns `Any[]` for unknown statement types.

Extend via `operands(::Block, s::MyType)` for domain-specific IR nodes.
"""
operands(block::Block, inst::Instruction) = operands(block, inst[:stmt])

operands(::Block, s::PiNode) = Any[s.val]
operands(::Block, s::ControlFlowOp) = operands(s)
# A `ReturnNode` reads the value it returns, except in its unreachable form, which
# has no `val` at all. This mirrors how `walk_uses!` treats it, so that `operands`
# and the use index agree on what a return reads.
operands(::Block, s::ReturnNode) = isdefined(s, :val) ? Any[s.val] : Any[]
# Alias statements (stmt IS a value) forward the value itself as their sole operand.
operands(::Block, s::SSAValue) = Any[s]
operands(::Block, s::BlockArgument) = Any[s]
operands(::Block, s::Argument) = Any[s]
operands(::Block, s::SlotNumber) = Any[s]
function operands(::Block, s::Expr)
    if s.head === :call
        return @view s.args[2:end]
    elseif s.head === :invoke
        return @view s.args[3:end]
    elseif s.head === :new || s.head === :splatnew
        return @view s.args[2:end]
    else
        return s.args
    end
end
operands(::Block, @nospecialize(_)) = Any[]


#=============================================================================
 Definition lookup
=============================================================================#

"""
    def(root, val::Core.SSAValue) -> Union{Instruction, Nothing}

Find the instruction that defines `val`. Performs a linear scan over
all blocks. The instruction's `block` field gives the containing block.
For repeated queries, build an index via [`defs`](@ref) instead.
"""
function def(root::Union{Block, StructuredIRCode}, val::Core.SSAValue)
    blk = root isa StructuredIRCode ? root.entry : root
    target = val.id
    for b in eachblock(blk)
        for inst in instructions(b)
            inst.ssa_idx == target && return inst
        end
    end
    return nothing
end

"""
    DefIndex

Pre-built index mapping SSA indices to their defining `Instruction`.
Build via `defs(root)`, query via `def(idx, val)`.
Analogous to `UseIndex` / `uses(block)`.
"""
struct DefIndex
    map::Dict{Int, Instruction}
end

"""
    defs(root) -> DefIndex

Build a definition index for all instructions in `root` (recursively).
Returns a `DefIndex` that supports O(1) lookup via `def(idx, val)`.

Analogous to `uses(block)` which returns a `UseIndex`.
"""
function defs(root::Union{Block, StructuredIRCode})
    blk = root isa StructuredIRCode ? root.entry : root
    map = Dict{Int, Instruction}()
    for b in eachblock(blk)
        for inst in instructions(b)
            map[inst.ssa_idx] = inst
        end
    end
    return DefIndex(map)
end

"""
    def(idx::DefIndex, val::Core.SSAValue) -> Union{Instruction, Nothing}

O(1) lookup of the instruction defining `val`.
"""
def(idx::DefIndex, val::Core.SSAValue) = get(idx.map, val.id, nothing)

Base.haskey(idx::DefIndex, val::Core.SSAValue) = haskey(idx.map, val.id)


#=============================================================================
 Scope queries
=============================================================================#

"""
    is_defined_outside(val, block::Block) -> Bool
    is_defined_outside(val, op::ForOp) -> Bool
    is_defined_outside(val, op::WhileOp) -> Bool
    is_defined_outside(val, op::LoopOp) -> Bool

Check whether `val` is defined outside a block (and all its descendants),
or outside a loop operation's regions.

The loop-op overloads handle values that are conceptually "inside" the loop
but not stored in a block's args, such as `ForOp.iv_arg`.

`Argument`s (function parameters), constants, `GlobalRef`s, and other
non-SSA values are always considered outside.

Analogous to MLIR's `LoopLikeOpInterface::isDefinedOutsideOfLoop`.
"""
function is_defined_outside(@nospecialize(val), block::Block)
    if val isa SSAValue || val isa BlockArgument
        for b in eachblock(block)
            val ∈ b && return false
        end
        return true
    else
        return true
    end
end

function is_defined_outside(@nospecialize(val), op::ForOp)
    val === op.iv_arg && return false
    return is_defined_outside(val, op.body)
end

function is_defined_outside(@nospecialize(val), op::WhileOp)
    return is_defined_outside(val, op.before) && is_defined_outside(val, op.after)
end

function is_defined_outside(@nospecialize(val), op::LoopOp)
    return is_defined_outside(val, op.body)
end


#=============================================================================
 Instruction movement
=============================================================================#

"""
    move_before!(inst::Instruction, target::Instruction) -> Instruction

Move `inst` from its current block to just before `target` in `target`'s block.
The instruction retains its SSA index, statement, type, and flags. Sub-block
parents are updated if the instruction is a `ControlFlowOp`. Returns a fresh
handle pointing into the destination block.

Analogous to MLIR's `Operation::moveBefore`.
"""
function move_before!(inst::Instruction, target::Instruction)
    src = inst.block
    dst = target.block
    entry = src.body[inst.ssa_idx]

    delete!(src.body, inst.ssa_idx)
    insert_before_idx!(dst.body, target.ssa_idx, inst.ssa_idx,
                       entry.stmt, entry.type, entry.flag)

    if entry.stmt isa ControlFlowOp
        for b in blocks(entry.stmt)
            b.parent = dst
        end
    end
    return Instruction(inst.ssa_idx, dst)
end

"""
    move_after!(inst::Instruction, target::Instruction) -> Instruction

Move `inst` from its current block to just after `target` in `target`'s block.
The instruction retains its SSA index, statement, type, and flags. Sub-block
parents are updated if the instruction is a `ControlFlowOp`. Returns a fresh
handle pointing into the destination block.

Analogous to MLIR's `Operation::moveAfter`.
"""
function move_after!(inst::Instruction, target::Instruction)
    src = inst.block
    dst = target.block
    entry = src.body[inst.ssa_idx]

    delete!(src.body, inst.ssa_idx)
    insert_after_idx!(dst.body, target.ssa_idx, inst.ssa_idx,
                      entry.stmt, entry.type, entry.flag)

    if entry.stmt isa ControlFlowOp
        for b in blocks(entry.stmt)
            b.parent = dst
        end
    end
    return Instruction(inst.ssa_idx, dst)
end


#=============================================================================
 Static-eval helpers
=============================================================================#

"""
    const_value(sci::StructuredIRCode, x) -> Union{Some, Nothing}

Return `Some(value)` when `x`'s value is statically known in `sci`,
otherwise `nothing`. The Julia analog of `static_eval` in `codegen.cpp`:
dispatches on every operand-position IR shape, recovers the value from
inference's lattice when it's a `Const` or singleton, and returns the
literal itself otherwise.

`GlobalRef` lookups are anchored on `sci.valid_worlds` (captured at
structurization from `IRCode.valid_worlds`) and read only binding-
partition metadata, never `getfield(mod, name)`. So on 1.12+ this
neither triggers the "access-to-binding-prior-to-its-definition-world"
warning nor reflects post-inference rebinds.

This is the static-value view over [`argextype`](@ref); call `value_type`
for the widened type instead.
"""
const_value(sci::StructuredIRCode, @nospecialize(x)) = from_type(argextype(sci, x))

"""
    argextype(src, val) -> Any

Inferred lattice element for an operand-position IR value, either a
`Compiler.Const(v)` (statically known value), a widened `Type`, or
`nothing` for inference artifacts (`MethodInstance`/`CodeInstance`) and
unresolvable `SSAValue`/`Argument` tags. Mirrors `Core.Compiler.argextype`
against `StructuredIRCode`-shaped IR.

`src` selects the SSA lookup strategy: a `Block` walks the parent chain
(structured scoping); a `StructuredIRCode` does a flat scan via [`def`](@ref).

Consumers go through [`value_type`](@ref) (widened type) or
[`const_value`](@ref) (static value when known).
"""
function argextype(src::Union{Block,StructuredIRCode}, @nospecialize(val))
    val isa BlockArgument && return val.type
    val isa Undef && return val.type
    val isa Instruction && return val[:type]
    # `MethodInstance` and `CodeInstance` appear as the first operand of
    # `:invoke` Exprs but they're inference artifacts, not values. Match
    # `static_eval` (codegen.cpp) by rejecting them explicitly so they don't
    # fall through to the literal branch.
    (val isa Core.MethodInstance || val isa Core.CodeInstance) && return nothing
    val isa QuoteNode && return CC.Const(val.value)
    val isa SSAValue && return _argextype_ssa(src, val)
    # The remaining shapes need access to `sci.argtypes`/`sci.valid_worlds`.
    sci = src isa StructuredIRCode ? src : root(src)
    val isa Argument && return 1 <= val.n <= length(sci.argtypes) ? sci.argtypes[val.n] : nothing
    val isa SlotNumber && return 1 <= val.id <= length(sci.argtypes) ? sci.argtypes[val.id] : nothing
    val isa GlobalRef && return global_lattice_element(val, sci.valid_worlds.max_world)
    # Anything else is a literal; wrap as `Const` so widenconst / from_type
    # recover `typeof(val)` / `Some(val)` respectively.
    return CC.Const(val)
end

# SSA type lookup: parent-chain walk (Block, structured scope) vs.
# flat scan via `def` (SCI, no scope info available).
function _argextype_ssa(block::Block, val::SSAValue)
    entry = get(block.body, val.id, nothing)
    entry !== nothing && return entry.type
    p = block.parent
    while p isa Block
        entry = get(p.body, val.id, nothing)
        entry !== nothing && return entry.type
        p = p.parent
    end
    return nothing
end

function _argextype_ssa(sci::StructuredIRCode, val::SSAValue)
    inst = def(sci, val)
    inst === nothing ? nothing : inst[:type]
end

# Internal: recover the value from a type slot. Handles both
# `Compiler.Const(val)` (inference-narrowed to a specific value) and
# singleton ghost types (one-instance types like `typeof(sin)`).
# Mirrors `singleton_type` + `Const`-unwrap in one helper.
function from_type(@nospecialize(rt))
    rt === nothing && return nothing
    rt isa CC.Const && return Some(rt.val)
    if rt isa Type && isdefined(rt, :instance)
        return Some(rt.instance)
    end
    return nothing
end

# Internal: read a `GlobalRef`'s inferred lattice element at `world`.
# Mirrors `Core.Compiler.abstract_eval_globalref_type`. Lattice elements
# aren't part of the public surface; consumers go through `const_value`.
@static if VERSION >= v"1.12-"
    function global_lattice_element(g::GlobalRef, world::UInt)
        binding = convert(Core.Binding, g)
        partition = CC.lookup_binding_partition(world, binding)
        (_, (leaf_binding, leaf_partition)) =
            CC.walk_binding_partition(binding, partition, world)
        return CC.abstract_eval_partition_load(nothing, leaf_binding, leaf_partition).rt
    end
else
    # 1.11 lacks the binding-partition API. Delegate to the existing
    # `abstract_eval_globalref_type`, which returns `Const(value)` for
    # const bindings, the binding's declared type otherwise: the same
    # `from_type`-friendly shape as the 1.12+ path. Reading via
    # `getfield(mod, name)` unconditionally would erase the const-vs-
    # mutable distinction (every binding becomes `Const`), which lets
    # mutable host globals leak into kernel IR as compile-time values.
    global_lattice_element(g::GlobalRef, ::UInt) =
        CC.abstract_eval_globalref_type(g)
end
