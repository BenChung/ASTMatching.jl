module ASTMatching
using Tries
struct UnionType{Base, Key, Arg} end

# Write your package code here.
include("patterns.jl")
include("treegen.jl")
include("useful.jl")
include("codegen.jl")
include("macros.jl")
end
