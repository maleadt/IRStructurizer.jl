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

 A try is then three sets of blocks (`try_info`):

     B ── MEnter ──body──▶ R   blocks entered with the handler active
                 └─catch─▶ C   blocks the catch block dominates that run on B's
                               own handler stack before the catch's
                               `pop_exception`, minus the `:leave` blocks that pop
                               one of B's outer handlers

 Every edge out of R starts at a `:leave` block, and every edge out of R ∪ C lands
 on a block with B's handler stack.
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

#=============================================================================
 Try regions
=============================================================================#

"""
    TryRegion

One try, by its `MEnter`. `enter` is the `MEnter` id (the `TryOp`'s SSA index) and
`block` the block it terminates. `body` (R) holds the blocks entered with this
handler active. `handler` (C) holds the blocks the catch block dominates that run
on `block`'s handler stack, minus the `:leave` blocks that pop one of the outer
handlers. It is empty for a scope-only enter. `depth` is the handler-stack depth
at `block`'s entry.
"""
struct TryRegion
    enter::Int
    block::Int
    body::Set{Int}
    handler::Set{Int}
    depth::Int
end

construct_blocks(r::TryRegion) = union(r.body, r.handler)

# A block holding only a `:leave` that pops one of the handlers in `outer`. It
# belongs to the enclosing try body, not to the handler region that reaches it.
function is_outer_leave(b::MBlock, outer::Vector{Int})
    length(b.body) == 1 || return false
    st = b.body[1].stmt
    is_leave(st) || return false
    return any(a -> a isa SSAValue && a.id in outer, st.args)
end

"""
    try_info(m, stacks=handler_stacks(m), domtree=...) -> Dict{Int, TryRegion}

The `TryRegion` of every reachable `MEnter`, keyed by the `MEnter` id.

A handler region ends where its exception is popped. When the protected body
cannot complete normally (it always throws, or loops forever), the catch block
dominates all the code after the handler, so dominance alone would pull that code
in, and with it every continuation `normalize_one_try!` builds. So a block is in the
handler only if it is entered with the exception state of this catch, or of a catch
nested in it (`exception_states`), not the state `pop_exception` restores, or if it
lies inside a try entered within the catch. An exit out of such a try pops the
catch's exception before it leaves the try (`break` out of `catch; try ... end`),
and the leave block that follows is still part of the handler.
"""
function try_info(m::MCFG, stacks=handler_stacks(m),
                  domtree::DomTree=construct_domtree(build_cfg(m)))
    regions = Dict{Int, TryRegion}()
    enter_block = Dict{Int, Int}(b.term.id => bid for (bid, b) in enumerate(m.blocks)
                                 if b.term isa MEnter && stacks[bid] !== nothing)
    estate, at_enter = exception_states(m, enter_block)
    for (bid, b) in enumerate(m.blocks)
        t = b.term
        t isa MEnter || continue
        σ = stacks[bid]
        σ === nothing && continue
        body = Set{Int}()
        handler = Set{Int}()
        for (x, s) in enumerate(stacks)
            s === nothing && continue
            t.id in s && push!(body, x)
        end
        if t.catch_dest != 0
            c = t.catch_dest
            d = length(σ)
            for (x, s) in enumerate(stacks)
                s === nothing && continue
                (length(s) >= d && view(s, 1:d) == σ) || continue
                dominates(domtree, c, x) || continue
                # Code inside a try entered within this catch stays in the handler
                # even past the catch's pop: Julia may pop before leaving that try.
                (in_catch(estate[x], t.id, at_enter) ||
                 (length(s) > d && in_catch(get(at_enter, s[d+1], -1), t.id, at_enter))) || continue
                is_outer_leave(m.blocks[x], σ) && continue
                push!(handler, x)
            end
        end
        regions[t.id] = TryRegion(t.id, bid, body, handler, length(σ))
    end
    return regions
end

"""Whether exception state `s` lies inside the catch of the enter `e`: it is `e`'s own
state, or that of a catch nested in it (whose enter ran in state `e`)."""
function in_catch(s::Int, e::Int, at_enter::Dict{Int, Int})
    for _ in 0:length(at_enter)       # the states form a tree; bound the walk anyway
        s == e && return true
        s <= 0 && return false
        s = get(at_enter, s, 0)
    end
    return false
end

"""The edges that leave a try's body and handler (R ∪ C). Each lands on a block that
holds the try block's handler stack; together they are the `TryOp`'s continuation."""
function try_exit_refs(m::MCFG, r::TryRegion)
    construct = construct_blocks(r)
    refs = EdgeRef[]
    for src in sort!(collect(construct))
        for ref in _edge_refs_of(src, m.blocks[src].term)
            edge_of(m, ref).target in construct || push!(refs, ref)
        end
    end
    return refs
end

is_pop_exception(@nospecialize(s)) =
    s isa Expr && s.head === :pop_exception && length(s.args) == 1 && s.args[1] isa SSAValue

"""
    exception_states(m, enter_block) -> (state at each block's entry, state at each enter)

The exception-stack state, as in the second component of Julia's
`compute_trycatch`: the id of the `MEnter` whose catch region the code is in (0
outside every catch). The catch edge of an `MEnter` sets it to that enter's id, and
`pop_exception %X` restores the state that `X` was entered with.
"""
function exception_states(m::MCFG, enter_block::Dict{Int, Int})
    nb = length(m.blocks)
    state = fill(-1, nb)          # -1: not reached yet
    at_enter = Dict{Int, Int}()
    state[m.entry] = 0
    work = Int[m.entry]
    while !isempty(work)
        b = pop!(work)
        s = state[b]
        blk = m.blocks[b]
        for st in blk.body
            is_pop_exception(st.stmt) || continue
            x = st.stmt.args[1].id
            haskey(enter_block, x) || continue
            s = get(at_enter, x, s)
        end
        t = blk.term
        t isa MEnter && (at_enter[t.id] = s)
        for tgt in _term_targets(t)
            s′ = (t isa MEnter && tgt == t.catch_dest && tgt != t.body.target) ? t.id : s
            if state[tgt] == -1
                state[tgt] = s′
                push!(work, tgt)
            end
        end
    end
    return state, at_enter
end

#=============================================================================
 Placing pop_exception

 Each `pop_exception` should run at the handler depth and in the exception state
 of the catch it pops: inside that catch's handler region, where its own enter
 dominates it. Julia orders pops and leaves either way around; these rewrites
 move the pops into place.
=============================================================================#

"""Move the `pop_exception`s that open a block reached only through `:leave`s to
before those leaves, when the leaves took the handler stack below the depth of
the catch whose exception they pop. Julia leaves an enclosing try and then pops
when a catch exits past it (`try; try ... catch; return x; end ... end`:
`leave %outer`, then `pop_exception %inner`). The pop then sits outside the outer
try, where the lift puts it after the outer `TryOp`, and possibly after a loop
around that `TryOp`, where no enter that could name it dominates it. Before the
leave, the pop is back in the inner catch, where its own enter dominates it. A
leave pops the handler stack and a pop restores the exception stack, so the two
commute. Run before `split_leaves!`; `sink_pops_below_leaves!` then moves a pop
that went past more leaves than needed back down to its catch's depth."""
function hoist_pops_over_leaves!(m::MCFG)
    changed = true
    while changed
        changed = false
        stacks = handler_stacks(m)
        enter_depth = Dict{Int, Int}()
        for (bid, b) in enumerate(m.blocks)
            b.term isa MEnter && stacks[bid] !== nothing &&
                (enter_depth[b.term.id] = length(stacks[bid]::Vector{Int}))
        end
        incoming = [Int[] for _ in m.blocks]   # the source block of each edge
        catch_dests = Set{Int}()
        for (bid, b) in enumerate(m.blocks)
            t = b.term
            if t isa MGoto
                push!(incoming[t.edge.target], bid)
            elseif t isa MCondBr
                push!(incoming[t.t.target], bid); push!(incoming[t.f.target], bid)
            elseif t isa MEnter
                push!(incoming[t.body.target], bid)
                t.catch_dest != 0 && push!(catch_dests, t.catch_dest)
            end
        end
        for (pid, p) in enumerate(m.blocks)
            srcs = incoming[pid]
            (isempty(srcs) || pid == m.entry || pid in catch_dests) && continue
            stacks[pid] === nothing && continue
            depth = length(stacks[pid]::Vector{Int})
            # The leading pops of a catch deeper than this block (`nothing`
            # placeholders may sit between them).
            n = 0
            while n < length(p.body) &&
                  (is_pop_exception(p.body[n+1].stmt) || p.body[n+1].stmt === nothing)
                n += 1
            end
            n == 0 && continue
            pops = MStmt[s for s in view(p.body, 1:n) if is_pop_exception(s.stmt) &&
                         get(enter_depth, s.stmt.args[1].id, depth) > depth]
            isempty(pops) && continue
            all(srcs) do src
                b = m.blocks[src]
                b.term isa MGoto && !isempty(b.body) && is_leave(b.body[end].stmt)
            end || continue
            for (j, src) in enumerate(srcs)
                b = m.blocks[src]
                moved = j == 1 ? pops : map(pops) do s
                    id = alloc_id!(m)
                    m.types[id] = s.type
                    m.codelocs[id] = s.codeloc
                    MStmt(id, s.stmt, s.type, s.codeloc, s.flag)
                end
                for s in moved
                    insert!(b.body, length(b.body), s)    # before the leave
                end
            end
            moved_ids = Set{Int}(s.id for s in pops)
            filter!(s -> !(s.id in moved_ids), p.body)
            changed = true
        end
    end
    return m
end

"""Move a `pop_exception` that runs before leaving trys entered in its catch to
after those leaves, back at the depth of the catch. Julia pops first when a catch
exits through a try nested in it (`catch; try; ...; continue; catch; end`: the
`continue` pops the outer exception, then leaves the inner try). The inner try's
continuation then joins that exit, whose exception is already popped, with the
inner handler's exit, which still holds it. No exception state fits the join, so
the outer handler region would grow over the continuation, and over the
continuation of the next mux, without end when the catch dominates them (a body
that cannot complete normally).

Runs after `split_leaves!`. The pop moves only along the chain of leave blocks
that follows it and nothing else reaches, into a new block after the last leave
it has to pass. Blocks holding nothing but pops may sit between it and the leaves
(`split_pops_across_catches!` puts the pop of each outer catch in one). Their pops
move too, in order, and keep a block each, so the split stays."""
function sink_pops_below_leaves!(m::MCFG)
    stacks = handler_stacks(m)
    enter_depth = Dict{Int, Int}()
    for (bid, b) in enumerate(m.blocks)
        b.term isa MEnter && stacks[bid] !== nothing &&
            (enter_depth[b.term.id] = length(stacks[bid]::Vector{Int}))
    end
    npreds = zeros(Int, length(m.blocks))
    for b in m.blocks, tgt in _term_targets(b.term)
        npreds[tgt] += 1
    end
    for bid in 1:length(m.blocks)          # range fixed: new blocks hold placed pops
        b = m.blocks[bid]
        (stacks[bid] === nothing || !(b.term isa MGoto)) && continue
        depth = length(stacks[bid]::Vector{Int})
        # The trailing pops (`nothing` placeholders may sit between them), each
        # with the number of leaves it has to pass. Their order is kept, so the
        # numbers may only grow along the run.
        k = length(b.body)
        while k >= 1 && (is_pop_exception(b.body[k].stmt) || b.body[k].stmt === nothing)
            k -= 1
        end
        k == length(b.body) && continue
        # Each pop with the number of leaves it has to pass and the block it is in.
        npops(stmts, from) = [(s, depth - get(enter_depth, s.stmt.args[1].id, depth), from)
                              for s in stmts if is_pop_exception(s.stmt)]
        pops = npops(view(b.body, k+1:length(b.body)), bid)
        # The blocks of pops alone that follow, into which `split_pops_across_catches!`
        # put the pops of the outer catches, continue the run.
        cur = b.term.edge.target
        while true
            l = m.blocks[cur]
            (npreds[cur] == 1 && l.term isa MGoto && any(s -> is_pop_exception(s.stmt), l.body) &&
             all(s -> is_pop_exception(s.stmt) || s.stmt === nothing, l.body)) || break
            append!(pops, npops(l.body, cur))
            cur = l.term.edge.target
        end
        filter!(p -> p[2] > 0, pops)
        isempty(pops) && continue
        issorted(pops; by=p -> p[2]) || continue
        chain = Int[]
        while length(chain) < pops[end][2]
            l = m.blocks[cur]
            (npreds[cur] == 1 && length(l.body) == 1 && is_leave(l.body[1].stmt) &&
             l.term isa MGoto) || break
            push!(chain, cur)
            cur = l.term.edge.target
        end
        length(chain) >= pops[end][2] || continue
        # The pops of one block go to one new block, and the split pops keep a
        # block each, in order, so each exit still holds the state it held.
        last_placed = Dict{Int, Int}()       # leaves passed => last block placed there
        placed = Dict{Tuple{Int, Int}, Int}()
        for (s, n, from) in pops
            nb = get!(placed, (n, from)) do
                l = m.blocks[get(last_placed, n, chain[n])]
                id = add_block!(m, MBlock(Int[], MStmt[], l.term, l.term_codeloc, l.term_id))
                l.term = MGoto(MEdge(id))
                l.term_id = 0
                last_placed[n] = id
            end
            push!(m.blocks[nb].body, s)
        end
        moved = Set{Int}(s.id for (s, _) in pops)
        for x in unique(p[3] for p in pops)
            filter!(s -> !(s.id in moved), m.blocks[x].body)
        end
    end
    return m
end

"""Split a `pop_exception` that leaves several catches at once into one pop per
catch, each on the way out of its catch. Julia pops straight to the state an
exit needs: a `break` from a catch nested in another catch pops the outer
catch's exception, which drops the inner one too. The inner try's exits then
disagree on the exception state: that `break` leaves the inner handler with
nothing pending, while an exit from the inner body (a `return`, whose pop comes
after it) still holds the outer exception. Their join, the inner try's
continuation, would fall out of the outer catch's handler region, and the code
after it with it. With `pop_exception %inner` in the inner catch and
`pop_exception %outer` in a new block after it, every exit of the inner handler
holds the outer exception, as the exits of its body do.

Applies to the pops that end a block whose terminator is a goto; the extra pops
go to a chain of new blocks on that edge. The state comes from `exception_states`,
which keeps the first state that reaches a block, so a block is split only when
the enter of every catch it gains a pop for dominates it: no path then reaches it
without having entered that catch's try. Runs after `split_leaves!` and before
`sink_pops_below_leaves!`, which then moves each of the pops after the leaves
that follow it, to the handler depth of its own catch."""
function split_pops_across_catches!(m::MCFG)
    enter_block = Dict{Int, Int}(b.term.id => bid for (bid, b) in enumerate(m.blocks)
                                 if b.term isa MEnter)
    state, at_enter = exception_states(m, enter_block)
    domtree = construct_domtree(build_cfg(m))
    # Whether exception state `s` lies inside the catch of the enter `x`.
    nested_in(s, x) = s != x && in_catch(s, x, at_enter)
    for bid in 1:length(m.blocks)          # range fixed: new blocks hold single pops
        b = m.blocks[bid]
        (state[bid] < 0 || !(b.term isa MGoto)) && continue
        k = length(b.body)
        while k >= 1 && (is_pop_exception(b.body[k].stmt) || b.body[k].stmt === nothing)
            k -= 1
        end
        k == length(b.body) && continue
        # The state before the trailing pops.
        s = state[bid]
        for st in view(b.body, 1:k)
            is_pop_exception(st.stmt) || continue
            s = get(at_enter, st.stmt.args[1].id, s)
        end
        # One pop per catch left, innermost first.
        pops = Tuple{Int, MStmt}[]          # (catch, original pop it comes from)
        for st in view(b.body, k+1:length(b.body))
            is_pop_exception(st.stmt) || continue
            x = st.stmt.args[1].id
            haskey(at_enter, x) || (push!(pops, (x, st)); continue)
            while nested_in(s, x)
                push!(pops, (s, st))
                s = at_enter[s]
            end
            push!(pops, (x, st))
            s = at_enter[x]
        end
        count(is_pop_exception(st.stmt) for st in view(b.body, k+1:length(b.body))) ==
            length(pops) && continue        # nothing to split
        all(((x, _),) -> !haskey(enter_block, x) || dominates(domtree, enter_block[x], bid),
            pops) || continue
        stmts = map(enumerate(pops)) do (j, (x, st))
            id = j == 1 ? st.id : alloc_id!(m)
            if j > 1
                m.types[id] = st.type
                m.codelocs[id] = st.codeloc
            end
            MStmt(id, Expr(:pop_exception, SSAValue(x)), st.type, st.codeloc, st.flag)
        end
        resize!(b.body, k)
        push!(b.body, stmts[1])
        prev = bid
        for st in view(stmts, 2:length(stmts))
            p = m.blocks[prev]
            nb = add_block!(m, MBlock(Int[], MStmt[st], p.term, p.term_codeloc, p.term_id))
            p.term = MGoto(MEdge(nb))
            p.term_id = 0
            prev = nb
        end
    end
    return m
end

#=============================================================================
 Values undefined on the catch path
=============================================================================#

"""Turn the `Union{}`-typed phis and `PhiCNode`s that try/catch leaves behind into
explicit `Undef`. A variable that is never assigned on the path into a catch block
gets a `Union{}` PhiC, and phis carry that around merges and loops. A `Union{}`
value never exists at runtime: Julia only reads such a variable behind
`throw_undef_if_not`. Each edge operand that carries one becomes `Undef`, and each
upsilon of one becomes an undefined upsilon. The `Union{}` phis are then left
without any value: those that no statement, branch, return or scope reads are
dropped, so that the lift does not give a loop or `IfOp` a `Union{}` carry (a
statement that reads one is unreachable, and keeps it)."""
function undef_bottom_values!(m::MCFG)
    bottom = Set{Int}()
    for b in m.blocks
        for a in b.args
            get(m.types, a, Any) === Union{} && push!(bottom, a)
        end
        for s in b.body
            s.stmt isa Core.PhiCNode && s.type === Union{} && push!(bottom, s.id)
        end
    end
    isempty(bottom) && return
    isbottom(@nospecialize(v)) = v isa SSAValue && v.id in bottom
    for b in m.blocks
        t = b.term
        edges = t isa MGoto ? (t.edge,) : t isa MCondBr ? (t.t, t.f) :
                t isa MEnter ? (t.body,) : ()
        for e in edges
            targs = m.blocks[e.target].args
            for k in eachindex(e.args)
                isbottom(e.args[k]) && (e.args[k] = Undef(get(m.types, targs[k], Any)))
            end
        end
        for (i, s) in enumerate(b.body)
            if s.stmt isa Core.UpsilonNode && isdefined(s.stmt, :val) && isbottom(s.stmt.val)
                b.body[i] = MStmt(s.id, Core.UpsilonNode(), s.type, s.codeloc, s.flag)
            end
        end
    end
    # The `Union{}` block arguments nothing reads: out of their blocks and edges.
    read = Set{Int}()
    note(@nospecialize(v)) = (v isa SSAValue && push!(read, v.id); v)
    incoming = [MEdge[] for _ in m.blocks]
    for b in m.blocks
        for s in b.body
            remap_ssa(s.stmt, note)
        end
        t = b.term
        t isa MCondBr && note(t.cond)
        t isa MReturn && t.has_val && note(t.val)
        t isa MEnter && has_scope(t) && note(t.scope)
        for e in _term_edges(t)
            push!(incoming[e.target], e)
        end
    end
    for (bid, b) in enumerate(m.blocks)
        dead = findall(a -> a in bottom && !(a in read), b.args)
        isempty(dead) && continue
        deleteat!(b.args, dead)
        for e in incoming[bid]
            deleteat!(e.args, dead)
        end
    end
end
