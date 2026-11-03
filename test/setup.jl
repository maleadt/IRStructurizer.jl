const CC = Core.Compiler
using Core: Argument

# Build an IRCode from explicit blocks. Each block is `(stmts, succs)`:
#   stmts :: Vector of (stmt, type)  — SSA indices are assigned in this order
#   succs :: Vector{Int}             — successor block indices (1-based)
# Predecessors are derived from succs. `argtypes[1]` is the closure-self type.
function build_ir(blocks::Vector, argtypes::Vector)
    nstmts = sum(length(b.stmts) for b in blocks)
    # Build the InstructionStream from flat vectors via its bulk constructor.
    # The per-statement `Instruction` proxy with `inst[:field] = ...` only exists
    # on 1.12+, whereas the bulk constructor is shared across supported versions.
    all_stmts = Vector{Any}(undef, nstmts)
    all_types = Vector{Any}(undef, nstmts)
    all_flags = fill(CC.IR_FLAGS_EFFECTS, nstmts)
    info = CC.CallInfo[CC.NoCallInfo() for _ in 1:nstmts]
    line = fill(Int32(0), nstmts * (VERSION >= v"1.12-" ? 3 : 1))
    ranges = UnitRange{Int}[]
    pos = 0
    for b in blocks
        start = pos + 1
        for (s, t) in b.stmts
            pos += 1
            all_stmts[pos] = s
            all_types[pos] = t
        end
        push!(ranges, start:pos)
    end
    stmts = CC.InstructionStream(all_stmts, all_types, info, line, all_flags)
    nb = length(blocks)
    preds = [Int[] for _ in 1:nb]
    for (i, b) in enumerate(blocks), s in b.succs
        push!(preds[s], i)
    end
    bbs = [CC.BasicBlock(CC.StmtRange(first(ranges[i]), last(ranges[i])),
                         preds[i], copy(blocks[i].succs)) for i in 1:nb]
    cfg = CC.CFG(bbs, Int[first(r) for r in ranges[2:end]])
    @static if VERSION >= v"1.12-"
        return CC.IRCode(stmts, cfg, CC.DebugInfoStream(line), argtypes, Expr[], CC.VarState[])
    else
        return CC.IRCode(stmts, cfg, Core.LineInfoNode[], argtypes, Expr[], CC.VarState[])
    end
end

# Total emitted occurrences of each statement matching `pred`, recursively
# across all nested control-flow blocks (invariant I2: no duplication).
function count_stmts(blk::Block, pred)
    n = 0
    for (_, entry) in blk.body
        pred(entry.stmt) && (n += 1)
        if entry.stmt isa ControlFlowOp
            for sub in IRStructurizer.blocks(entry.stmt)
                n += count_stmts(sub, pred)
            end
        end
    end
    return n
end

# The name of the global a call head reads: a `GlobalRef`, or the binding
# partition Julia 1.14 resolves one to.
callee_name(ref::GlobalRef) = ref.name
callee_name(@nospecialize(ref)) = IRStructurizer.is_binding_partition(ref) ?
    Base.partition_owner(ref).globalref.name : nothing

iscall_to(stmt, fname::Symbol) =
    stmt isa Expr && stmt.head === :call && !isempty(stmt.args) &&
    callee_name(stmt.args[1]) === fname

# A partition held as a constant: inference types `holds_partition`'s
# statements `Const(COPY_PARTITION)`.
const COPY_PARTITION = isdefined(Core, :getglobal_partition) ?
    Base.lookup_binding_partition(Base.get_world_counter(), GlobalRef(Base, :Inf)) : nothing
@noinline fetch_partition() = (print(devnull, ""); COPY_PARTITION)
holds_partition(x) = (fetch_partition(), x)

# Globals holding a function, for `resolve_callee` on binding partitions.
partition_callee(x) = x + 1
const partition_callee_const = partition_callee
global partition_callee_typed::typeof(partition_callee) = partition_callee
partition_callee_untyped = partition_callee

#=============================================================================
 Round-trip harness: run a function and its structurized, lowered copy on the
 same inputs and compare what they do (julialowering_cases.jl, exceptions.jl,
 julialowering_exceptions.jl). `log` is the vector the test functions record
 their side effects in.
=============================================================================#

"""An exception, comparable across runs: its type and message."""
rt_payload(@nospecialize(e)) = (typeof(e), sprint(showerror, e))

"""The payloads of the exceptions on the stack, outermost first."""
rt_stack() = Any[rt_payload(x.exception) for x in current_exceptions()]

"""
    rt_outcome(log, f, args...)

What a call does: `(:ok, value)`, or `(:threw, payload, above)` with the exception
it threw and the ones it left on the exception stack above the caller's, outermost
first (the thrown one, after any it was handling when it threw); the entries it
made in `log`; how many exceptions it left on the stack after a normal return (-1
after a throw); and what changed in the part of the stack that was there before
the call (`prior`: each replaced entry, by its position from the top, and how many
were dropped; a `rethrow(e)` replaces the current exception, a pop too many drops
one). All of it is relative to the stack before the call: Julia 1.11 leaves the
exception on the stack when a `finally` returns after a throw, and leaked
exceptions stay there across calls.
"""
function rt_outcome(log::Vector{Any}, f, args...)
    empty!(log)
    depth = -1
    held = rt_stack()
    before = length(held)
    # What changed below `before`: replaced entries by their offset from the top
    # of that part, and the number of entries dropped.
    changes(stack) = (Any[(i - before, stack[i]) for i in 1:min(before, length(stack))
                          if stack[i] != held[i]],
                      before - min(before, length(stack)))
    result, prior = try
        v = f(args...)
        stack = rt_stack()
        depth = length(stack) - before
        (:ok, v), changes(stack)
    catch e
        stack = rt_stack()
        (:threw, rt_payload(e), stack[before+1:end]), changes(stack)
    end
    return (; result, log = copy(log), depth, prior)
end

"""`rt_outcome` for a call made while a catch is handling an exception: a pop that
also drops the caller's exception shows in the depth, or in the stack a throw
leaves."""
function rt_outcome_in_catch(log::Vector{Any}, f, args...)
    try
        throw(ErrorException("the caller's exception"))
    catch
        return rt_outcome(log, f, args...)
    end
end

"""Lower `sci` back to `IRCode`, check it with `verify_ir`, and compile it. This
runs outside `rt_outcome`, so a lowering failure is a test error, never an outcome
to compare."""
function rt_lower(sci::StructuredIRCode)
    ir = CC.IRCode(sci)
    CC.verify_ir(ir)
    ir = CC.copy(ir)
    ir.argtypes[1] = Tuple{}
    @static if VERSION >= v"1.12-"
        ir.debuginfo.def = Symbol("unstructurized")
    end
    return Core.OpaqueClosure(ir)
end

"""Run `f` and the lowered closure `oc` on every input tuple, directly and from
inside a catch (`rt_outcome`, `rt_outcome_in_catch`); returns the mismatches."""
function rt_compare(log::Vector{Any}, f, oc, inputs)
    problems = String[]
    for args in inputs, run in (rt_outcome, rt_outcome_in_catch)
        expected = run(log, f, args...)
        got = run(log, oc, args...)
        isequal(expected, got) && continue
        where = run === rt_outcome ? "" : " (in a catch)"
        push!(problems, "$(nameof(f))$(args)$(where): expected $(expected), got $(got)")
    end
    return problems
end
