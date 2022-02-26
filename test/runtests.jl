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

	@test ASTMatching.iswildcard(ASTMatching.StarPat())
	@test !ASTMatching.iswildcard(ASTMatching.VarPat(:test))
	

	@test ASTMatching.heads(ASTMatching.CstrPat(:head, [])) == Set{Symbol}([:head])
	@test ASTMatching.heads(
		ASTMatching.OrPat(
			ASTMatching.CstrPat(:head1, []),
			ASTMatching.CstrPat(:head2, []))) == Set{Symbol}([:head1, :head2])

	@test ASTMatching.extract_pattern(:a) == ASTMatching.VarPat(:a)
	@test ASTMatching.extract_pattern(:(_)) == ASTMatching.StarPat()
	@test ASTMatching.extract_pattern(:(C())) == ASTMatching.CstrPat(:C, [])
	@test ASTMatching.extract_pattern(:(C(a, _))) == ASTMatching.CstrPat(:C, [ASTMatching.VarPat(:a), ASTMatching.StarPat()])
	@test ASTMatching.extract_pattern(:(C(a, D()))) == ASTMatching.CstrPat(:C, [ASTMatching.VarPat(:a), ASTMatching.CstrPat(:D, [])])

	@test ASTMatching.extract_case(:(C() => 2+2)) == ([ASTMatching.CstrPat(:C, [])] => :(2+2))
	@test ASTMatching.extract_patterns(quote 
		C() => 2+2
	end) == [[ASTMatching.CstrPat(:C, [])] => :(2+2)]
	@test ASTMatching.extract_patterns(quote 
		C() => 2+2
		D(e) => 3+e
	end) == [
		[ASTMatching.CstrPat(:C, [])] => :(2+2),
		[ASTMatching.CstrPat(:D, [ASTMatching.VarPat(:e)])] => :(3+e)]

	preproc_pat, vars = ASTMatching.preprocess_variables(ASTMatching.extract_patterns(quote 
		C() => 2+2
		D(e) => 3+e
	end))
	@test haskey(vars, [1,1])
	@test vars[[1,1]] == last(preproc_pat[2]).args[1].args[2]

	preproc_pat, vars = ASTMatching.preprocess_variables(ASTMatching.extract_patterns(quote 
		(_, C()) => 2+2
		(_, D(e)) => 3+e
	end))
	@test haskey(vars, [2,1])
	@test vars[[2,1]] == last(preproc_pat[2]).args[1].args[2]

	@test ASTMatching.S(constructors, List, :Cons, 1, 
		[ASTMatching.Pat[ASTMatching.CstrPat(:Cons, [ASTMatching.StarPat(), ASTMatching.StarPat()])]], [1]) == [[ASTMatching.StarPat(), ASTMatching.StarPat()] => 1]
	@test ASTMatching.S(constructors, List, :Cons, 1, 
		[ASTMatching.Pat[ASTMatching.CstrPat(:Nil, [])]], [1]) == []
	@test ASTMatching.S(constructors, List, :Cons, 1, 
		[ASTMatching.Pat[ASTMatching.StarPat()]], [1]) == [[ASTMatching.StarPat(), ASTMatching.StarPat()] => 1]
	@test ASTMatching.S(constructors, List, :Cons, 1, 
		[ASTMatching.Pat[ASTMatching.OrPat(ASTMatching.StarPat(), ASTMatching.CstrPat(:Cons, [ASTMatching.StarPat(), ASTMatching.StarPat()]))]], [1]) == 
		[[ASTMatching.StarPat(), ASTMatching.StarPat()] => 1,
		 [ASTMatching.StarPat(), ASTMatching.StarPat()] => 1]


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
