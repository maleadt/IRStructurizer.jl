# Exact expansion of `ForOp` into the general structured ops.
#
# This is the reference lowering of the counted-range contract (see the `ForOp`
# docstring). `IRCode(::StructuredIRCode)` runs it before flattening, and a code
# generator without a native counted loop for a given `ForOp` can run it as its
# fallback instead of re-implementing inclusive ranges. It never computes
# `upper ± step`: an inclusive range stops on equality with `upper`, and an
# exclusive range's header test keeps its increment representable.

export expand_for_loops!

"""
    expand_for_loops!(sci::StructuredIRCode; validate=true) -> sci

Rewrite every `ForOp` in `sci`, innermost first, into the general ops:

- **inclusive**: an `IfOp` testing `lower <= upper` (signed or unsigned by the IV
  type) around a `LoopOp` that carries the original carries plus the IV. At every
  continuation of the loop the carried values are the source continuation's, in
  their original order; the IV is then compared with `upper`, and on equality the
  loop breaks with those values, otherwise it continues with them and the
  incremented IV. The else arm yields the initial carries. The `IfOp` takes over
  the `ForOp`'s SSA index and result type, so post-loop `getfield`s are unchanged;
  the internal IV result is projected away.
- **exclusive**: a `WhileOp` whose `before` region tests `iv < upper` with the
  matching signed or unsigned compare and whose `after` region is the body with
  `iv + step` computed before each continuation. The IV rides as the last carry,
  after the original ones, so the public result positions and the result type are
  unchanged.

A loop's result tuple may be a prefix of its carries (carries threaded through
an inner loop as invariants have no result slot); only that prefix is projected.

Only continuations of the expanded loop are rewritten; nested loops keep their own
terminators. Nested conditional continuations all get the same exit/update
sequence. Synthesized guards, compares and increments are anchored to the
`ForOp`'s source location. The result is validated (`validate`) and is not
re-promoted.
"""
function expand_for_loops!(sci::StructuredIRCode; validate::Bool=true)
    sci.entry.parent = sci
    fix_parents!(sci.entry)
    # Check the producer contract before expansion erases the ForOps.
    validate && validate_terminators(sci)
    expand_for_loops_in!(sci, sci.entry)
    if validate
        validate_scf(sci.entry)
        validate_no_phis(sci.entry)
        validate_terminators(sci)
        validate_ssa_defs(sci)
        validate_ssa_uniqueness(sci)
    end
    return sci
end

function expand_for_loops_in!(sci::StructuredIRCode, block::Block)
    # Snapshot the indices: expansion inserts statements and replaces the ForOp's
    # own entry, but the new ops contain no further ForOps.
    for idx in copy(block.body.ssa_idxes)
        stmt = block.body[idx].stmt
        if stmt isa ControlFlowOp
            for b in blocks(stmt)
                expand_for_loops_in!(sci, b)
            end
        end
        stmt isa ForOp && expand_forop!(sci, block, idx)
    end
end

"""Whether `sci` contains a `ForOp` anywhere."""
function has_forop(sci::StructuredIRCode)
    found = false
    walk(sci) do inst, _
        inst[:stmt] isa ForOp || return nothing
        found = true
        return :interrupt
    end
    return found
end

"""Anchor a synthesized statement's debug info to an existing SSA index (same
semantics as the structurizer's `anchor_line!`: a positive entry is followed)."""
function anchor_line!(sci::StructuredIRCode, new_ssa::Int, source_ssa::Int)
    haskey(sci.line_map, source_ssa) || return
    sci.line_map[new_ssa] = source_ssa
end

alloc_ssa!(sci::StructuredIRCode) = (sci.max_ssa_idx += 1)
alloc_arg!(sci::StructuredIRCode, @nospecialize(T)) = BlockArgument(sci.max_arg_idx += 1, T)

"""The blocks whose terminator continues the loop owning `body`: `body` itself
and any `IfOp` arm reached without entering a nested loop."""
function continuation_blocks(block::Block, out::Vector{Block}=Block[])
    block.terminator isa ContinueOp && push!(out, block)
    for (_, entry) in block.body
        entry.stmt isa IfOp || continue
        continuation_blocks(entry.stmt.then_region, out)
        continuation_blocks(entry.stmt.else_region, out)
    end
    return out
end

"""
    expand_forop!(sci, block, idx)

Expand the `ForOp` at `block[idx]` in place (see [`expand_for_loops!`](@ref)).
"""
function expand_forop!(sci::StructuredIRCode, block::Block, idx::Int)
    entry = block.body[idx]
    op = entry.stmt::ForOp
    T = forop_iv_type(op.iv_arg.type)
    T === nothing && error("ForOp at %$idx: induction variable type $(op.iv_arg.type) is not a concrete BitInteger")
    signed = forop_iv_signed(T)
    newop = op.inclusive ? expand_inclusive!(sci, block, idx, op, entry.type, T, signed) :
                           expand_exclusive!(sci, block, idx, op, entry.type, T, signed)
    for b in blocks(newop)
        b.parent = block
        fix_parents!(b)
    end
    return newop
end

function expand_inclusive!(sci::StructuredIRCode, block::Block, idx::Int, op::ForOp,
                           @nospecialize(result_type), T::DataType, signed::Bool)
    iv = op.iv_arg
    body = op.body
    carry_types = Any[a.type for a in body.args]
    result_types = ifop_expected_yield_types(result_type)
    nresults = result_types === nothing ? length(carry_types) : length(result_types)

    # Latch: after the continuation's own values, stop on `iv === upper`, else
    # advance. Both arms diverge, so the continuation block ends in the dispatch.
    for blk in continuation_blocks(body)
        vals = (blk.terminator::ContinueOp).values
        eq = alloc_ssa!(sci)
        push!(blk, eq, Expr(:call, GlobalRef(Core, :(===)), iv, op.upper), Bool)
        anchor_line!(sci, eq, idx)
        done = Block()
        done.terminator = BreakOp(IRValue[vals..., iv])
        next = Block()
        inc = alloc_ssa!(sci)
        push!(next, inc, Expr(:call, GlobalRef(Base, :add_int), iv, op.step), T)
        anchor_line!(sci, inc, idx)
        next.terminator = ContinueOp(IRValue[vals..., SSAValue(inc)])
        dispatch = alloc_ssa!(sci)
        push!(blk, dispatch, IfOp(SSAValue(eq), done, next), Nothing)
        anchor_line!(sci, dispatch, idx)
        blk.terminator = nothing
    end

    # The loop carries the IV last, after the original carries; its results are
    # the public prefix, so the IV is projected away.
    push!(body.args, iv)
    loop = LoopOp(body, IRValue[op.init_values..., op.lower])
    loop_idx = alloc_ssa!(sci)
    then_blk = Block()
    push!(then_blk, loop_idx, loop, Tuple{carry_types[1:nresults]...})
    anchor_line!(sci, loop_idx, idx)
    results = IRValue[]
    for i in 1:nresults
        r = alloc_ssa!(sci)
        push!(then_blk, r, Expr(:call, Core.getfield, SSAValue(loop_idx), i), carry_types[i])
        anchor_line!(sci, r, idx)
        push!(results, SSAValue(r))
    end
    then_blk.terminator = YieldOp(results)
    else_blk = Block()
    else_blk.terminator = YieldOp(IRValue[op.init_values[1:nresults]...])

    # Entry guard `lower <= upper`, then the IfOp at the ForOp's own index.
    guard = alloc_ssa!(sci)
    cmp = GlobalRef(Base, signed ? :sle_int : :ule_int)
    insert_before_idx!(block.body, idx, guard, Expr(:call, cmp, op.lower, op.upper), Bool)
    anchor_line!(sci, guard, idx)
    newop = IfOp(SSAValue(guard), then_blk, else_blk)
    block[idx] = (; stmt=newop, type=result_type)
    return newop
end

function expand_exclusive!(sci::StructuredIRCode, block::Block, idx::Int, op::ForOp,
                           @nospecialize(result_type), T::DataType, signed::Bool)
    iv = op.iv_arg
    body = op.body
    carry_types = Any[a.type for a in body.args]

    # Increment before every continuation; the body's own becomes the yield.
    for blk in continuation_blocks(body)
        vals = (blk.terminator::ContinueOp).values
        inc = alloc_ssa!(sci)
        push!(blk, inc, Expr(:call, GlobalRef(Base, :add_int), iv, op.step), T)
        anchor_line!(sci, inc, idx)
        next = IRValue[vals..., SSAValue(inc)]
        blk.terminator = blk === body ? YieldOp(next) : ContinueOp(next)
    end
    push!(body.args, iv)

    # Header: fresh args (each region owns its own), `iv < upper`.
    before = Block()
    for ty in carry_types
        push!(before.args, alloc_arg!(sci, ty))
    end
    before_iv = alloc_arg!(sci, T)
    push!(before.args, before_iv)
    test = alloc_ssa!(sci)
    cmp = GlobalRef(Base, signed ? :slt_int : :ult_int)
    push!(before, test, Expr(:call, cmp, before_iv, op.upper), Bool)
    anchor_line!(sci, test, idx)
    before.terminator = ConditionOp(SSAValue(test), IRValue[before.args...])

    # The IV result is the last carry, past the public prefix: the type stays.
    newop = WhileOp(before, body, IRValue[op.init_values..., op.lower])
    block[idx] = (; stmt=newop, type=result_type)
    return newop
end
