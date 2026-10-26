#=============================================================================
 Exception handling on the MCFG.

 Julia's IR expresses try/catch with an `EnterNode` terminator (push a handler,
 fall through into the protected region, with an implicit edge to the catch
 block), `Expr(:leave, enters...)` (pop handlers), `Expr(:pop_exception, enter)`
 (restore the exception stack), and `UpsilonNode`/`PhiCNode` pairs that carry
 values into the catch block. With `exceptions=:structured`, `ingest` turns the
 `EnterNode` into an `MEnter` terminator and gives every `:leave` a block of its
 own that pops one handler (`split_leaves!`). `handler_stacks` is the forward
 dataflow over those pushes and pops: the handlers active at each block's entry.
=============================================================================#

is_leave(@nospecialize(s)) = s isa Expr && s.head === :leave

"""Whether some block ends in an `MEnter` (set by `ingest`, see `MCFG`)."""
has_enter(m::MCFG) = m.has_eh

"""
    handler_stacks(m::MCFG) -> Vector{Union{Nothing, Vector{Int}}}

The active handlers at each block's entry, as the ids of their `MEnter`s,
outermost first (`nothing` for an unreachable block). This is the forward dataflow
of Julia's `compute_trycatch`. An `MEnter` pushes its id onto the stack of its
body edge, and its catch edge keeps the stack it was entered with. A `:leave`
pops one handler per argument. Throws `UnstructuredControlFlowError` when two
paths reach a block with different stacks (an unbalanced try/catch).
"""
function handler_stacks(m::MCFG)
    nb = length(m.blocks)
    stacks = Vector{Union{Nothing, Vector{Int}}}(nothing, nb)
    stacks[m.entry] = Int[]
    work = Int[m.entry]
    while !isempty(work)
        b = pop!(work)
        s = copy(stacks[b]::Vector{Int})
        blk = m.blocks[b]
        for st in blk.body
            is_leave(st.stmt) || continue
            n = length(st.stmt.args)
            n <= length(s) || throw(UnstructuredControlFlowError(
                "unbalanced try/catch: the :leave at %$(st.id) pops more handlers than are active"))
            resize!(s, length(s) - n)
        end
        t = blk.term
        if t isa MEnter
            _flow_stack!(stacks, work, t.body.target, push!(copy(s), t.id))
            t.catch_dest != 0 && _flow_stack!(stacks, work, t.catch_dest, s)
        else
            for tgt in _term_targets(t)
                _flow_stack!(stacks, work, tgt, s)
            end
        end
    end
    return stacks
end

function _flow_stack!(stacks, work::Vector{Int}, tgt::Int, s::Vector{Int})
    cur = stacks[tgt]
    if cur === nothing
        stacks[tgt] = copy(s)
        push!(work, tgt)
    elseif cur != s
        throw(UnstructuredControlFlowError(
            "unbalanced try/catch: block $tgt is entered with different active handlers"))
    end
end

"""Handler-stack depth at each block's entry (-1 for an unreachable block). An edge
into a shallower block leaves a try body."""
handler_depths(m::MCFG) = handler_depths(handler_stacks(m))
handler_depths(stacks::Vector) = Int[s === nothing ? -1 : length(s) for s in stacks]

"""Give every `:leave` a block of its own that pops one handler. Julia ends a block
at each `:leave`, which may pop several handlers at once (a `return` out of nested
trys). The leave moves to a chain of new blocks that pop the handlers innermost
first, each naming the `MEnter` it pops. A block ending in a leave then no longer
crosses a try boundary partway: everything before the leave is in the try body,
and the leave block's one outgoing edge is the exit. Runs after edge operands are
filled, since the moved terminator keeps its operands. A catch block that holds
nothing but a leave (a handler that exits an outer try at once) is split too, so
the handler region keeps its entry block."""
function split_leaves!(m::MCFG)
    stacks = handler_stacks(m)
    catch_dests = Set{Int}(b.term.catch_dest for b in m.blocks if b.term isa MEnter)
    for bid in 1:length(m.blocks)              # range fixed: new blocks are already split
        b = m.blocks[bid]
        k = findfirst(s -> is_leave(s.stmt), b.body)
        k === nothing && continue
        k == length(b.body) || throw(UnstructuredControlFlowError(
            "the :leave at %$(b.body[k].id) does not end its block"))
        stacks[bid] === nothing && continue      # unreachable: never lifted
        s = stacks[bid]::Vector{Int}
        leave = b.body[k]
        n = length(leave.stmt.args)
        if length(b.body) == 1 && n == 1 && !(bid in catch_dests)
            # Already a single-pop leave block. Name the handler it actually pops.
            b.body[1] = MStmt(leave.id, Expr(:leave, SSAValue(s[end])), leave.type,
                              leave.codeloc, leave.flag)
            continue
        end
        pop!(b.body)
        term, term_codeloc, term_id = b.term, b.term_codeloc, b.term_id
        prev = bid
        for j in 1:n
            id = j == 1 ? leave.id : alloc_id!(m)
            if j > 1
                m.types[id] = leave.type
                m.codelocs[id] = leave.codeloc
            end
            stmt = MStmt(id, Expr(:leave, SSAValue(s[end - j + 1])), leave.type,
                         leave.codeloc, leave.flag)
            nb = add_block!(m, MBlock(Int[], MStmt[stmt], MReturn(), leave.codeloc))
            m.blocks[prev].term = MGoto(MEdge(nb))
            m.blocks[prev].term_codeloc = leave.codeloc
            m.blocks[prev].term_id = 0
            prev = nb
        end
        m.blocks[prev].term = term
        m.blocks[prev].term_codeloc = term_codeloc
        m.blocks[prev].term_id = term_id
    end
end
