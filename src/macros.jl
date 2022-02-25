struct Case 
	name::Symbol
	key::Symbol
	arg_names::Vector{Symbol}
	arg_typs::Vector{Any}
end
struct MatchType
	name::Symbol
	base::Any
	key::Symbol
	arguments::Symbol
	cstrs::Vector{Case}
end
function parse_constructor(expr)
	@assert(expr.head == :call)
	case_desc = expr.args[1]
	@assert(case_desc.head == :curly)
	case_name = case_desc.args[1]
	case_key = case_desc.args[2]
	arg_typs = Any[]
	arg_names = Symbol[]
	for (index, arg) in enumerate(expr.args[2:end])
		@assert(arg.head == :(::))
		if (length(arg.args) == 1)
			push!(arg_names, Symbol("_" * string(index)))
			push!(arg_typs, arg.args[1])
		elseif (length(arg.args) == 2)
			push!(arg_names, arg.args[1])
			push!(arg_typs, arg.args[2])
		end
	end
	return Case(case_name, case_key.value, arg_names, arg_typs)
end
function parse_constructors(expr)
	@assert(expr.head == :block)
	cstrs = Case[]
	for stmt in expr.args
		if !(stmt isa LineNumberNode || (stmt isa Expr && stmt.head == :call))
			throw("Invalid constructor declaration $stmt")
		end
		if stmt isa LineNumberNode continue end
		push!(cstrs, parse_constructor(stmt))
	end
	return cstrs
end
function parse_definition(expr)
	@assert(expr.head == :(=))
	name_defn = expr.args[1]
	@assert(name_defn.head == :curly)
	name = name_defn.args[1]
	basetype = eval(name_defn.args[2])
	keyname = name_defn.args[3]
	argsname = name_defn.args[4]
	print(expr.args[2])
	cstrs = parse_constructors(expr.args[2])
	return MatchType(name, basetype, keyname, argsname, cstrs)
end
function _matchtype(typedecl, cstrs)
	@assert(typedecl.head == :(<:))
	tyname = typedecl.args[1]
	host_decl = typedecl.args[2]
	@assert(host_decl isa Expr)
	@assert(host_decl.head == :curly)
	hostname = host_decl.args[1]
	tykey = host_decl.args[2]
	tyargs = host_decl.args[3]
	cases = parse_constructors(cstrs)

    expr = Expr(:toplevel)
    
    constructor_heads = getproperty.(cases, :name)
    case_keys = getproperty.(cases, :key)
    constructor_arguments = getproperty.(cases, :arg_typs)
    constructor_pairs = Pair.(constructor_heads, constructor_arguments)
    key_pairs = Pair.(constructor_heads, case_keys)

    push!(expr.args, quote	
    	const $tyname = ASTMatching.UnionType{$hostname, $tykey, $tyargs}
	end)
    push!(expr.args, quote	
    	headof(e::$tyname) = e.$tykey
	end)
    push!(expr.args, quote	
    	argof(e::$tyname, i) = e.$tyargs[i]
	end)
    push!(expr.args, quote	
    	constructors(::Type{$tyname}) = Dict($(constructor_pairs...))
	end)
	push!(expr.args, quote
		constructor_keys(::Type{$tyname}) = Dict($(key_pairs...))
	end)
    return esc(expr)
end
macro matchtype(typedecl, cstrs)
	return _matchtype(typedecl, cstrs)
end

#=
pat ::= 
	_ => Str
	x => Var{:x}
	C(pat...) => Cstr{:key, Tuple{pat...}}
	pat || pat => Or{pat, pat}
=#

@generated function _matchfun(receiver::T) where T
end

macro astmatch(discriminant, patterns)
	_compile(patterns)
end
