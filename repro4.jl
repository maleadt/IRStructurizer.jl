using IRStructurizer
CC = Core.Compiler
function execute(sci, args...)
    ir = CC.copy(CC.IRCode(sci)); ir.argtypes[1] = Tuple{}
    VERSION >= v"1.12-" && (ir.debuginfo.def = Symbol("x"))
    Core.OpaqueClosure(ir)(args...)
end
function judge(name, f, sig, inputs)
    local sci
    try
        sci = (code_structured(f, sig) |> only).first
    catch e
        println(rpad(name,34), " LOUD (structurize): ", first(sprint(showerror,e),50)); return
    end
    nwrong=0; nfail=0
    for args in inputs
        exp = f(args...)
        got = try execute(sci, args...) catch; nfail+=1; continue end
        got==exp || (nwrong+=1)
    end
    status = nwrong>0 ? "*** SILENT MISCOMPILE ($nwrong/$(length(inputs))) ***" :
             nfail>0 ? "LOUD (exec $nfail)" : "ok"
    println(rpad(name,34), " ", status)
end

ii = [(p,n) for p in (false,true) for n in (0,1,2,3,5)]

# A: single loop, two value-carrying breaks (no nesting)
judge("A two-val-breaks", (p::Bool,n::Int)->begin s=0; for k in 1:n
    if p; s=8; break; end; if k>2; s=2; break; end; s+=k; end; s end, Tuple{Bool,Int}, ii)

# B: single loop, plain break + value-break
judge("B plain+val break", (p::Bool,n::Int)->begin s=0; for k in 1:n
    if p; break; end; if k>2; s=2; break; end; s+=k; end; s end, Tuple{Bool,Int}, ii)

# C: single loop, two plain breaks
judge("C two plain breaks", (p::Bool,n::Int)->begin s=0; for k in 1:n
    if p; break; end; if k>2; break; end; s+=k; end; s end, Tuple{Bool,Int}, ii)

# D: single loop, break + early return
judge("D break+return", (p::Bool,n::Int)->begin s=0; for k in 1:n
    if p; return -1; end; if k>2; break; end; s+=k; end; s end, Tuple{Bool,Int}, ii)

# E: single loop, one value break only
judge("E one val break", (p::Bool,n::Int)->begin s=0; for k in 1:n
    if k>2; s=99; break; end; s+=k; end; s end, Tuple{Bool,Int}, ii)

# F: inner-loop break (nested)
judge("F inner-loop break", (p::Bool,n::Int)->begin s=0; for k in 1:n
    for j in 1:n; if j>k; break; end; s+=j; end; end; s end, Tuple{Bool,Int}, ii)
