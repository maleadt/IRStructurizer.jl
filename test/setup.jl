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
    # on 1.12+, whereas this constructor (and the 3-per-stmt packed `line`) is
    # shared, matching production `_assemble`.
    all_stmts = Vector{Any}(undef, nstmts)
    all_types = Vector{Any}(undef, nstmts)
    all_flags = fill(CC.IR_FLAGS_EFFECTS, nstmts)
    info = CC.CallInfo[CC.NoCallInfo() for _ in 1:nstmts]
    line = fill(Int32(0), nstmts * 3)
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
    cfg = CC.CFG(bbs, Int[first(r) for r in ranges])
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

iscall_to(stmt, fname::Symbol) =
    stmt isa Expr && stmt.head === :call && !isempty(stmt.args) &&
    (c = stmt.args[1]; c isa GlobalRef && c.name === fname)
