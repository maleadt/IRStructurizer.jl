using IRStructurizer
using Base: code_ircode
CC = Core.Compiler
function execute(sci, args...)
    ir = CC.copy(CC.IRCode(sci)); ir.argtypes[1] = Tuple{}
    VERSION >= v"1.12-" && (ir.debuginfo.def = Symbol("x"))
    Core.OpaqueClosure(ir)(args...)
end

rng = Ref(0x12345678_9abcdef0 % UInt64)
nextu() = (rng[] = rng[]*0x5851f42d4c957f2d + 0x14057b7ef767814f; rng[] >> 33)
ri(n) = Int(nextu() % n); pick(xs) = xs[ri(length(xs))+1]

# Generate loop bodies that include break (with/without carried value) and nested loops.
function gstmt(d, ind, depth)
    pad = "  "^ind; c = ri(depth<=0 ? 4 : 6)
    if c==0; "$(pad)s += k"
    elseif c==1; "$(pad)s += $(ri(5)+1)"
    elseif c==2; "$(pad)if k > $(ri(5)); break; end"          # plain break
    elseif c==3; "$(pad)if k > $(ri(5)); s = $(ri(9)); break; end"  # break carrying value
    elseif c==4
        v="j$(depth)"
        "$(pad)for $v in 1:k\n$(join([gstmt(d-1,ind+1,depth-1) for _ in 1:(ri(2)+1)],"\n"))\n$(pad)end"
    else
        "$(pad)if $(pick(["p","k>2","k<n"]))\n$(join([gstmt(d-1,ind+1,depth) for _ in 1:(ri(2)+1)],"\n"))\n$(pad)end"
    end
end

ok=0; loud=0; silent=0; total=0
for i in 1:120
    body = join([gstmt(2,1,2) for _ in 1:(ri(3)+1)], "\n")
    src = "function _lf$i(p::Bool, n::Int)\n s=0\n for k in 1:n\n$body\n end\n return s\nend"
    f = try eval(Meta.parse(src)) catch; continue end
    local sci
    try
        sci = (code_structured(f, Tuple{Bool,Int}) |> only).first
    catch
        global loud += 1; continue
    end
    for p in (false,true), n in (0,1,3,5)
        global total += 1
        exp = try Base.invokelatest(f,p,n) catch; continue end
        got = try execute(sci,p,n) catch; global loud; continue end
        if got==exp; global ok+=1
        else
            global silent+=1
            if silent <= 3
                println("SILENT MISCOMPILE in _lf$i(p=$p,n=$n): got $got exp $exp")
                println(src); println("---")
            end
        end
    end
end
println("loop-fuzz: structurize_loud_fail=$loud  exec_checks=$total  ok=$ok  SILENT=$silent")
