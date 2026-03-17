using PrecompileTools

@setup_workload begin
    @compile_workload begin
        # Exercise the main API with a simple if-then-else pattern
        code_structured(Tuple{Int}) do x::Int
            x > 0 ? x + 1 : x - 1
        end

        # Exercise a loop pattern
        code_structured(Tuple{Int}) do n::Int
            i = 0
            while i < n
                i += 1
            end
            return i
        end
    end
end
