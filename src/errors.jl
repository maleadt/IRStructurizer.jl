# error types used across the package

export UnstructuredControlFlowError, UnsubstitutedPhiError, InvalidTerminatorError,
       UndefinedSSAError

"""
Exception thrown when unstructured control flow is detected in structured IR.
"""
struct UnstructuredControlFlowError <: Exception
    stmt_indices::Vector{Int}
end

function Base.showerror(io::IO, e::UnstructuredControlFlowError)
    print(io, "UnstructuredControlFlowError: unstructured control flow at statement(s): ",
          join(e.stmt_indices, ", "))
end

"""
Exception thrown when phi nodes remain after block arg substitution.
"""
struct UnsubstitutedPhiError <: Exception
    stmt_indices::Vector{Int}
end

function Base.showerror(io::IO, e::UnsubstitutedPhiError)
    print(io, "UnsubstitutedPhiError: phi nodes remain at statement(s): ",
          join(e.stmt_indices, ", "))
end

"""
Exception thrown when structured control flow ops have invalid terminators.
"""
struct InvalidTerminatorError <: Exception
    messages::Vector{String}
end

function Base.showerror(io::IO, e::InvalidTerminatorError)
    print(io, "InvalidTerminatorError: ")
    for (i, msg) in enumerate(e.messages)
        i > 1 && print(io, "; ")
        print(io, msg)
    end
end

"""
Exception thrown when SSA values are used but never defined in the structured IR.
"""
struct UndefinedSSAError <: Exception
    undefined::Vector{Int}
end

function Base.showerror(io::IO, e::UndefinedSSAError)
    print(io, "UndefinedSSAError: SSA values used but not defined: ",
          join(("%$id" for id in e.undefined), ", "))
end
