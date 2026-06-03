using PrecompileTools

@setup_workload begin
    @compile_workload begin
        # if-then-else
        code_structured(Tuple{Int}) do x::Int
            x > 0 ? x + 1 : x - 1
        end

        # loop
        code_structured(Tuple{Int}) do n::Int
            i = 0
            while i < n
                i += 1
            end
            return i
        end
    end
end
