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
    constructor_pairs = map((head, typ)->:($head => [$(typ...)]), QuoteNode.(constructor_heads), constructor_arguments)
    key_pairs = Pair.(constructor_heads, case_keys)

    push!(expr.args, quote	
    	const $tyname = ASTMatching.UnionType{$hostname, $tykey, $tyargs}
	end)
    push!(expr.args, quote	
    	headof(::Type{$tyname}, e::$hostname) = e.$(tykey.value)
	end)
    push!(expr.args, quote	
    	argof(::Type{$tyname}, e::$hostname, i) = e.$(tyargs.value)[i]
	end)
    push!(expr.args, quote	
    	args(::Type{$tyname}, e::$hostname,) = e.$(tyargs.value)
	end)
    push!(expr.args, quote	
    	constructors(::Type{$tyname}) = Dict($(constructor_pairs...))
	end)
	push!(expr.args, quote
		constructor_keys(::Type{$tyname}) = Dict($(key_pairs...))
	end)
	push!(expr.args, quote
		@generated keytype(t::Type{$tyname}) = :(fieldtype($(Expr(:$, :t)), $tykey))
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


macro astmatch(discriminant, patterns)
	preproc_pat, callbacks, vars = ASTMatching.preprocess_variables(ASTMatching.extract_patterns(patterns))
	println(vars)
	matchfun = gensym("match")
	extracted_disc = Any[]
	extracted_disc_tys = Any[]
	function parse_discriminant(expr)
		@assert(expr.head == :(::))
		return esc(expr.args[1]), esc(expr.args[2])
	end
	if discriminant isa Expr 
		if discriminant.head == :tuple
			combined = parse_discriminant.(discriminant.args)
			append!(extracted_disc, getindex.(combined, 1))
			append!(extracted_disc_tys, getindex.(combined, 2))
		elseif discriminant.head == :(::)
			disc,ty = parse_discriminant(discriminant)
			push!(extracted_disc, disc)
			push!(extracted_disc_tys, ty)
		else
			throw("discriminant must be a tuple or symbol") 
		end
	else
		throw("discriminant must be a tuple or symbol") 
	end
	base_occ = [[1] for disc in extracted_disc]
	argnms = [gensym() for arg in extracted_disc]
	argtys = [gensym() for arg in extracted_disc]
	args = [:($((argnm))::$argty) for (argnm, argty) in zip(argnms, argtys)]
	tyargnms = [gensym() for arg in extracted_disc]
	typ_args = [:(::Type{$tyargnm}) for (tyargnm, argty) in zip(tyargnms, argtys)]
	empty_typ_args = [:($tyargnm::Any) for (tyargnm, argty) in zip(tyargnms, argtys)]
	cstrs = (:constructors)
	cstr_keys = (:constructor_keys)
	tyargs = [:($tyargnm <: (ASTMatching.UnionType{$argty, K, A} where {K, A})) for (tyargnm, argty) in zip(tyargnms, argtys)]
	star_pat = Pat[StarPat() for arg in extracted_disc]
	pats_only = ASTMatching.patterns.(preproc_pat)

	callback_defns = [:(($((esc.(ASTMatching.vars(callback)))...), ) -> $(esc(expr(callback)))) for callback in callbacks]

	genfunc = quote 
		function $matchfun($(argnms...), $(empty_typ_args...), $(((name.(callbacks)))...)) 
			realtys = typeof.($argnms)
			argtys = [$(tyargnms...)]
			throw("Attempted to match on $realtys when expecting $argtys")
		end
		@generated function $matchfun($(args...), $(typ_args...), $(((name.(callbacks)))...)) where {$(argtys...), $(tyargs...)}
			ts = Type[$(tyargnms...)]
			useful = ASTMatching.useful($cstrs, $pats_only, $star_pat, ts)
			if useful 
				cex = ASTMatching.counterexample($cstrs, $pats_only, ts)
				throw("incomplete match counterexample: $cex")
			end
			compiled_match = ASTMatching.cc($cstrs, $base_occ, $preproc_pat, ts)
			return ASTMatching.toplevel_compile($cstr_keys, $cstrs, compiled_match, $argnms, $vars)
		end
	end
	__module__.eval(genfunc) 

	out= quote 
		$(esc(matchfun))($(extracted_disc...), $(extracted_disc_tys...), $(callback_defns...), )
	end
	return out
end