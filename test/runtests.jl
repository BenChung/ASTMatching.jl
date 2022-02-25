using ASTMatching
using Test

struct BaseStruct
	kind::Symbol
	arguments::Vector{Any}
end
@testset "ASTMatching.jl" begin
	ASTMatching.@matchtype List <: BaseStruct{:kind, :arguments} begin
		Cons{:cons}(next::List, body::String)
		Nil{:nil}()
	end
	@test List == ASTMatching.UnionType{BaseStruct, :kind, :arguments}
	@test constructors(List) == Dict([:Cons => Any[:List, :String], :Nil=>Any[]])
	@test constructor_keys(List) == Dict([:Cons => :cons, :Nil => :nil])

	@test ASTMatching.iswildcard(ASTMatching.StarPat)
	@test !ASTMatching.iswildcard(ASTMatching.VarPat{:test})
	

	@test ASTMatching.heads(ASTMatching.CstrPat{:head, 0, Tuple{}}) == Set{Symbol}([:head])
	@test ASTMatching.heads(
		ASTMatching.OrPat{
			ASTMatching.CstrPat{:head1, 0, Tuple{}},
			ASTMatching.CstrPat{:head2, 0, Tuple{}}}) == Set{Symbol}([:head1, :head2])

	@test ASTMatching.extract_pattern(:a) == ASTMatching.VarPat{:a}
	@test ASTMatching.extract_pattern(:(_)) == ASTMatching.StarPat
	@test ASTMatching.extract_pattern(:(C())) == ASTMatching.CstrPat{:C, 0, Tuple{}}
	@test ASTMatching.extract_pattern(:(C(a, _))) == ASTMatching.CstrPat{:C, 2, Tuple{ASTMatching.VarPat{:a}, ASTMatching.StarPat}}
	@test ASTMatching.extract_pattern(:(C(a, D()))) == ASTMatching.CstrPat{:C, 2, Tuple{ASTMatching.VarPat{:a}, ASTMatching.CstrPat{:D, 0, Tuple{}}}}

	@test ASTMatching.extract_case(:(C() => 2+2)) == (Tuple{ASTMatching.CstrPat{:C, 0, Tuple{}}} => :(2+2))
	@test ASTMatching.extract_patterns(quote 
		C() => 2+2
	end) == [(Tuple{ASTMatching.CstrPat{:C, 0, Tuple{}}} => :(2+2))]
	@test ASTMatching.extract_patterns(quote 
		C() => 2+2
		D(e) => 3+e
	end) == [
		(Tuple{ASTMatching.CstrPat{:C, 0, Tuple{}}} => :(2+2)),
		(Tuple{ASTMatching.CstrPat{:D, 1, Tuple{ASTMatching.VarPat{:e}}}} => :(3+e))]

	test_patterns = ASTMatching.extract_patterns(quote 
		C() => 2+2
		D(e) => 3+e
	end)
	ASTMatching.preprocess_variables(test_patterns)



	#=
pats = [Pat{Symbol}[CstrPat(:Cons, Pat{Symbol}[VarPat{Symbol}(:hii), CstrPat(:Cons, Pat{Symbol}[VarPat{Symbol}(:hello), VarPat{Symbol}(:hi)])])]=>1, 
        Pat{Symbol}[CstrPat{Symbol}(:Cons, Pat{Symbol}[VarPat{Symbol}(:hi), VarPat{Symbol}(:hii)])] => 2,
        Pat{Symbol}[CstrPat{Symbol}(:Nil, Pat{Symbol}[])] => 3]
match_mat, var_map = preprocess_variables(pats)
println(var_map)
match_tree = cc([[1], [1]], match_mat, [List])

make_inputs(1, var_map)
toplevel_compile(match_tree, [:x], var_map)
=#
end
