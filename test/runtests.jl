using ASTMatching
using Test

const APP = ASTMatching.ProcessedPattern
const APat = ASTMatching.Pat

struct BaseStruct
	kind::Symbol
	arguments::Vector{Any}
end

ASTMatching.@matchtype List <: BaseStruct{:kind, :arguments} begin
	Cons{:cons}(next::List, body::String)
	Nil{:nil}()
end

struct BaseASTStruct
	kind::Symbol
	arguments::Vector{Any}
end

ASTMatching.@matchtype ExampleAST <: BaseASTStruct{:kind, :arguments} begin
    BinOp{:binop}(left::ExampleAST, op::Symbol, right::ExampleAST)
    UnaryOp{:unop}(op::Symbol, expr::ExampleAST)
    Constant{:cnst}(op::Any)
end

struct BaseASTStruct2
    kind::Symbol
    arguments::Vector{Any}
end

ASTMatching.@matchtype ExampleAST2 <: BaseASTStruct2{:kind, :arguments} begin
    Block{:block}(body::Vector{ExampleAST2})
    Constant{:cnst}()
end

@testset "ASTMatching.jl" begin
	Pat = ASTMatching.Pat
	StarPat = ASTMatching.StarPat
	MultiStarPat = ASTMatching.MultiStarPat
	MultiVarPat = ASTMatching.MultiVarPat
	VarPat = ASTMatching.VarPat
	CstrPat = ASTMatching.CstrPat
	Fixed = ASTMatching.Fixed
	Expanding = ASTMatching.Expanding
	@test List == ASTMatching.UnionType{BaseStruct, :kind, :arguments}
	@test constructors(List) == Dict([:Cons => [List, String], :Nil=>Any[]])
	@test constructor_keys(List) == Dict([:Cons => :cons, :Nil => :nil])

	@test ASTMatching.iswildcard(StarPat())
	@test !ASTMatching.iswildcard(VarPat(:test))
	@test ASTMatching.iswildcard(MultiStarPat())
	

	@test ASTMatching.heads(CstrPat(:head, ASTMatching.Pat[])) == Set{Symbol}([:head])
	@test ASTMatching.heads(
		ASTMatching.OrPat(
			CstrPat(:head1, []),
			CstrPat(:head2, []))) == Set{Symbol}([:head1, :head2])

	@test ASTMatching.extract_pattern(:a) == VarPat(:a)
	@test ASTMatching.extract_pattern(:(_)) == StarPat()
	@test ASTMatching.extract_pattern(:(C())) == CstrPat(:C, [])
	@test ASTMatching.extract_pattern(:(C(a, _))) == CstrPat(:C, [VarPat(:a), StarPat()])
	@test ASTMatching.extract_pattern(:(C(a, D()))) == CstrPat(:C, [VarPat(:a), CstrPat(:D, [])])
	@test ASTMatching.extract_pattern(:(C(a, _))) == CstrPat(:C, [VarPat(:a), StarPat()])
	@test ASTMatching.extract_pattern(:(C(a, _))) == CstrPat(:C, [VarPat(:a), StarPat()])
	@test ASTMatching.extract_pattern(:(C(a, __))) == CstrPat(:C, [VarPat(:a), MultiStarPat()])
	@test ASTMatching.extract_pattern(:(C(a, b_))) == CstrPat(:C, [VarPat(:a), MultiVarPat(:b)])
	@test ASTMatching.extract_pattern(:(__)) == MultiStarPat()

	@test ASTMatching.extract_case(:(C() => 2+2)) == ASTMatching.MatchCase([CstrPat(:C, [])], :(2+2))
	@test ASTMatching.extract_case(:(C(__) => 2+2)) == ASTMatching.MatchCase([CstrPat(:C, [MultiStarPat()])], :(2+2))
	@test ASTMatching.extract_case(:(C(a_) => 2+2)) == ASTMatching.MatchCase([CstrPat(:C, [MultiVarPat(:a)])], :(2+2))
	@test ASTMatching.extract_patterns(quote 
		C() => 2+2
	end) == [ASTMatching.MatchCase([CstrPat(:C, [])], :(2+2))]
	@test ASTMatching.extract_patterns(quote 
		C() => 2+2
		D(e) => 3+e
	end) == 
		[ASTMatching.MatchCase([CstrPat(:C, [])], :(2+2)),
		 ASTMatching.MatchCase([CstrPat(:D, [VarPat(:e)])], :(3+e))]

	preproc_pat, callbacks, vars = ASTMatching.preprocess_variables(ASTMatching.extract_patterns(quote 
		C() => 2+2
		D(e) => 3+e
	end))
	@test haskey(vars, [ASTMatching.Index(1),ASTMatching.Index(1)])
	@test get(vars[ASTMatching.Index(1),ASTMatching.Index(1)]) == callbacks[2].expr.args[1].args[2]

	preproc_pat, callbacks, vars = ASTMatching.preprocess_variables(ASTMatching.extract_patterns(quote 
		(_, C()) => 2+2
		(_, D(e)) => 3+e
	end))
	@test haskey(vars, [ASTMatching.Index(2),ASTMatching.Index(1)])
	@test get(vars[ASTMatching.Index(2),ASTMatching.Index(1)]) == callbacks[2].expr.args[1].args[2]

	preproc_pat, callbacks, vars = ASTMatching.preprocess_variables(ASTMatching.extract_patterns(quote
	        (_, C()) => 2+2
	        (_, D(e, f_)) => 3+e
	end))
	@test haskey(vars,[ASTMatching.Index(2), ASTMatching.Star(2)] )
	@test get(vars[ASTMatching.Index(2), ASTMatching.Star(2)]) == callbacks[2].expr.args[1].args[2]

	@test ASTMatching.S(constructors, List, :Cons, Fixed(2), 1, 
		[APP(APat[CstrPat(:Cons, [StarPat(), StarPat()])], :a)]) ==
		[APP(APat[ASTMatching.StarPat(), ASTMatching.StarPat()], :a)]
	@test ASTMatching.S(constructors, List, :Cons, Fixed(2), 1, 
		[APP(APat[CstrPat(:Nil, [])], :a)]) == []
	@test ASTMatching.S(constructors, List, :Cons, Fixed(2), 1, 
		[APP(APat[StarPat()], :a)]) == 
		[APP(APat[StarPat(), StarPat()], :a)]
	@test ASTMatching.S(constructors, List, :Cons, Fixed(2), 1, 
		[APP(APat[ASTMatching.OrPat(StarPat(), CstrPat(:Cons, [StarPat(), StarPat()]))], :a)]) == 
		[APP(APat[StarPat(), StarPat()], :a),
		 APP(APat[StarPat(), StarPat()], :a)]

	@test ASTMatching.Dsingle(1, [APP(APat[StarPat()], :a)]) == [APP(APat[], :a)]
	@test ASTMatching.Dsingle(1, [APP(APat[CstrPat(:Nil, [])], :a)]) == []
	@test ASTMatching.Dsingle(1, [APP(APat[ASTMatching.OrPat(StarPat(), StarPat())], :a)]) ==
	                [APP(APat[], :a), APP(APat[], :a)]

	@test ASTMatching.cc(constructors, [[1]], [APP(APat[StarPat()], :a)], [List]) == ASTMatching.Leaf(:a)
	@test ASTMatching.cc(constructors, [[1]], [APP(APat[CstrPat(:Cons, Pat[StarPat(), StarPat()])], :a)], [List]) == 
		ASTMatching.Switch{List}([1], [(:Cons, Fixed(2)) => ASTMatching.Leaf(:a)], ASTMatching.Fail())
	@test ASTMatching.cc(constructors, [[1]], [
		APP(APat[CstrPat(:Cons, Pat[StarPat(), StarPat()])], :a),
		APP(APat[CstrPat(:Nil, Pat[])], :b)], [List]) == 
		ASTMatching.Switch{List}([1], [(:Cons, Fixed(2)) => ASTMatching.Leaf(:a), (:Nil, Fixed(0))=>ASTMatching.Leaf(:b)], nothing)

	# just make sure it doesn't error
	preproc_pat, callbacks, vars = ASTMatching.preprocess_variables(ASTMatching.extract_patterns(quote 
		Cons(a,b) => 2+2
		Nil() => 3+3
	end))
	match_tree = ASTMatching.cc(constructors, [[1]], preproc_pat, [List])
	ASTMatching.toplevel_compile(constructor_keys, constructors, match_tree, [:x], vars)
	@test ASTMatching.specialize_tyvect(constructors, Vector{ExampleAST2}, :Block, Type[Vector{ExampleAST2}], Pat[MultiStarPat()]) == [Vector{ExampleAST2}, Vector{ExampleAST2}]

	preproc_pat, callbacks, vars = ASTMatching.preprocess_variables(ASTMatching.extract_patterns(quote
	        Block(a, b) => 2+2
	        Block(a_) => 2+2
	        Constant() => 3+3
	end))
	match_tree = ASTMatching.cc(constructors, [[1]], preproc_pat, [ExampleAST2])
	ASTMatching.toplevel_compile(constructor_keys, constructors, match_tree, [:x], vars)

	# try the actual macro
	x = BaseStruct(:nil, [])
	result = (ASTMatching.@astmatch (x::List) begin 
		Cons(a,b) => 2+2
		Nil() => 3+3
	end)
	@test result == 6
	x = BaseStruct(:cons, [BaseStruct(:nil, []), "hello"])
	result = (ASTMatching.@astmatch (x::List) begin 
		Cons(a,b) => b
		Nil() => "hi"
	end)
	@test result == "hello"
	result = (ASTMatching.@astmatch (x::List) begin 
		Cons(Nil(),b) => b
		Cons(a,b) => "guten tag"
		Nil() => "hi"
	end)
	@test result == "hello"
	result = (ASTMatching.@astmatch (x::List) begin 
		Cons(a,b) => "guten tag"
		Cons(Nil(),b) => b
		Nil() => "hi"
	end)
	@test result == "guten tag"

	external = "guten tag"
	result = (ASTMatching.@astmatch (x::List) begin 
		Cons(a,b) => external
		Nil() => "hi"
	end)
	@test result == "guten tag"

	function testme(x)
		return (ASTMatching.@astmatch (x::List) begin 
			Cons(a,b) => b
			Nil() => "hi"
		end)
	end
	@test testme(x) == "hello"
	expr = BaseASTStruct(:cnst, [2])
	@test_throws(("Attempted to match on DataType[Symbol] when expecting DataType[ASTMatching.UnionType{BaseStruct, :kind, :arguments}]"),
		(ASTMatching.@astmatch (expr::List) begin 
			Cons(a,b) => external
			Nil() => "hi"
		end))

	@test (ASTMatching.@astmatch (expr::ExampleAST) begin
	    BinOp(left, op, right) => "binop"
	    UnaryOp(op, expr) => "unop"
	    Constant(cst) => "constant $cst"
	end) == "constant 2"

	@test (ASTMatching.@astmatch (expr::ExampleAST, x::List) begin
	    (BinOp(left, op, right), Cons(a,b)) => "binop, cons"
	    (BinOp(left, op, right), Nil()) => "binop, nil"
	    (UnaryOp(op, expr), l) => "unop"
	    (Constant(cst), l) => "constant $cst"
	end) == "constant 2"
	x = BaseStruct(:nil, [])
	expr = BaseASTStruct(:cnst, [2])
	@test_throws("incomplete match", (ASTMatching.@astmatch (expr::ExampleAST, x::List) begin
	    (BinOp(left, op, right), Cons(a,b)) => "binop, cons"
	    (UnaryOp(op, expr), l) => "unop"
	    (Constant(cst), l) => "constant $cst"
	end))

	expr2 = BaseASTStruct2(:block, [BaseASTStruct2(:cnst, [])])
    res = ASTMatching.@astmatch (expr2::ExampleAST2) begin
            Block(body_) => body
            Constant() => []
    end
    println(res)
    @test first(res) == first(expr2.arguments)

	expr = BaseASTStruct2(:block, [BaseASTStruct2(:cnst, []), BaseASTStruct2(:cnst, [])])
    res = ASTMatching.@astmatch (expr::ExampleAST2) begin
            Block(a, b) => a
            Block(body_) => body
            Constant() => []
    end
    @test first(res) == first(expr2.arguments)
end


@testset "Usefulness" begin
	Pat = ASTMatching.Pat
	StarPat = ASTMatching.StarPat
	VarPat = ASTMatching.VarPat
	CstrPat = ASTMatching.CstrPat
	@test !ASTMatching.useful(constructors, [Pat[CstrPat(:Cons, [StarPat(), StarPat()])], Pat[CstrPat(:Nil, [])]], Pat[StarPat()], Type[List])
	@test ASTMatching.useful(constructors, [Pat[CstrPat(:Cons, [StarPat(), StarPat()])]], Pat[StarPat()], Type[List])
	@test ASTMatching.useful(constructors, Vector{Pat}[], Pat[StarPat()], Type[List])
	@test ASTMatching.useful(constructors, Vector{Pat}[
		[CstrPat(:Cons, Pat[StarPat(), StarPat()]), CstrPat(:Cons, Pat[StarPat(), StarPat()])],
		[CstrPat(:Cons, Pat[StarPat(), StarPat()]), CstrPat(:Nil, Pat[])]], Pat[StarPat(), StarPat()], Type[List, List])
	basis =  Vector{Pat}[
		Pat[ASTMatching.CstrPat(:BinOp, Pat[ASTMatching.StarPat(), ASTMatching.StarPat(), ASTMatching.StarPat()]),
  	  		ASTMatching.CstrPat(:Cons, Pat[ASTMatching.StarPat(), ASTMatching.StarPat()])],
  		Pat[ ASTMatching.CstrPat(:UnaryOp, Pat[ASTMatching.StarPat(), ASTMatching.StarPat()]), ASTMatching.StarPat()],
  		Pat[ ASTMatching.CstrPat(:Constant, Pat[ASTMatching.StarPat()]), ASTMatching.StarPat()]]
	@test ASTMatching.useful(constructors, basis, Pat[StarPat(), StarPat()], Type[ExampleAST, List])
end

@testset "Counterexamples" begin
	Pat = ASTMatching.Pat
	StarPat = ASTMatching.StarPat
	VarPat = ASTMatching.VarPat
	CstrPat = ASTMatching.CstrPat
    basis =  Vector{Pat}[
        Pat[ASTMatching.CstrPat(:BinOp, Pat[ASTMatching.StarPat(), ASTMatching.StarPat(), ASTMatching.StarPat()]),
                ASTMatching.CstrPat(:Cons, Pat[ASTMatching.StarPat(), ASTMatching.StarPat()])],
        Pat[ ASTMatching.CstrPat(:UnaryOp, Pat[ASTMatching.StarPat(), ASTMatching.StarPat()]), ASTMatching.StarPat()],
        Pat[ ASTMatching.CstrPat(:Constant, Pat[ASTMatching.StarPat()]), ASTMatching.StarPat()]]
	@test ASTMatching.counterexample(constructors, basis, Type[ExampleAST, List], 2) ==
    	ASTMatching.CounterPat[
            ASTMatching.CstrCounterPat(:BinOp, ASTMatching.CounterPat[ASTMatching.StarCounterPat(ExampleAST), ASTMatching.StarCounterPat(Symbol), ASTMatching.StarCounterPat(ExampleAST)], ExampleAST),
            ASTMatching.CstrCounterPat(:Nil, ASTMatching.CounterPat[], List)]
end