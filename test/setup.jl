const CC = Core.Compiler
using Core: Argument

# Build an IRCode from explicit blocks. Each block is `(stmts, succs)`:
#   stmts :: Vector of (stmt, type)  — SSA indices are assigned in this order
#   succs :: Vector{Int}             — successor block indices (1-based)
# Predecessors are derived from succs. `argtypes[1]` is the closure-self type.
function build_ir(blocks::Vector, argtypes::Vector)
    nstmts = sum(length(b.stmts) for b in blocks)
    stmts = CC.InstructionStream(nstmts)
    ranges = UnitRange{Int}[]
    pos = 0
    for b in blocks
        start = pos + 1
        for (s, t) in b.stmts
            pos += 1
            inst = stmts[pos]
            inst[:stmt] = s
            inst[:type] = t
            inst[:info] = CC.NoCallInfo()
            inst[:line] = (Int32(0), Int32(0), Int32(0))
            inst[:flag] = CC.IR_FLAGS_EFFECTS
        end
        push!(ranges, start:pos)
    end
    nb = length(blocks)
    preds = [Int[] for _ in 1:nb]
    for (i, b) in enumerate(blocks), s in b.succs
        push!(preds[s], i)
    end
    bbs = [CC.BasicBlock(CC.StmtRange(first(ranges[i]), last(ranges[i])),
                         preds[i], copy(blocks[i].succs)) for i in 1:nb]
    cfg = CC.CFG(bbs, Int[first(r) for r in ranges])
    debuginfo = CC.DebugInfoStream(Int32[0 for _ in 1:nstmts])
    return CC.IRCode(stmts, cfg, debuginfo, argtypes, Expr[], CC.VarState[])
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

iscall_to(stmt, fname::Symbol) =
    stmt isa Expr && stmt.head === :call && !isempty(stmt.args) &&
    (c = stmt.args[1]; c isa GlobalRef && c.name === fname)
