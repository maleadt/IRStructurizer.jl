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

        # try/catch
        code_structured(Tuple{Int}; exceptions=:structured) do x::Int
            try
                x > 0 ? x : error("negative")
            catch
                -1
            end
        end
    end
end
