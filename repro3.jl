using IRStructurizer
CC = Core.Compiler
function execute(sci, args...)
    ir = CC.copy(CC.IRCode(sci)); ir.argtypes[1] = Tuple{}
    VERSION >= v"1.12-" && (ir.debuginfo.def = Symbol("x"))
    Core.OpaqueClosure(ir)(args...)
end

function lf5(p::Bool, n::Int)
    s = 0
    for k in 1:n
        for j2 in 1:k
            s += k
        end
        if p
            if k > 0; s = 8; break; end
            if k > 3; break; end
        end
        if k > 2; s = 2; break; end
    end
    return s
end

function check(sci)
    nwrong = 0
    for p in (false,true), n in (0,1,2,3,5)
        exp = lf5(p,n)
        got = try execute(sci,p,n) catch e; "EXECFAIL" end
        mark = got==exp ? "ok" : "*** WRONG ***"
        got==exp || (nwrong += 1)
        println("lf5(p=$p, n=$n) = got $got  exp $exp   $mark")
    end
    return nwrong
end

sci, _ = code_structured(lf5, Tuple{Bool,Int}) |> only
println("=== validates & structurizes OK ===")
nwrong = check(sci)
println("\n#wrong = $nwrong")
