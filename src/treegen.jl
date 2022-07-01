struct ProcessedPattern
	patterns::Vector{Pat}
	callback::Any
end
struct Callback 
	name::Symbol
	vars::Vector{Symbol}
	expr::Any
end
name(c::Callback) = c.name
vars(c::Callback) = c.vars
expr(c::Callback) = c.expr
patterns(p::ProcessedPattern) = p.patterns
Base.:(==)(a::ProcessedPattern, b::ProcessedPattern) = all(a.patterns .== b.patterns) && a.callback == b.callback

abstract type DTree end
struct Leaf <: DTree
	term::Any
end
struct Fail <: DTree end

struct Switch{T} <: DTree
	occ::Vector{Int}
	cases::Vector{Pair{Symbol, DTree}}
	default::Union{DTree, Nothing}
end

Base.:(==)(a::Leaf, b::Leaf) = a.term == b.term
Base.:(==)(a::Fail, b::Fail) = true
Base.:(==)(a::Switch{T}, b::Switch{T}) where T = a.occ == b.occ && a.cases == b.cases && a.default == b.default

preprocess_variables(occ::Vector{Int}, p::StarPat, occMap::Dict{Vector{Int}, Symbol}) = (p, Dict{Symbol, Symbol}())
preprocess_variables(occ::Vector{Int}, v::VarPat, occMap::Dict{Vector{Int}, Symbol}) = (StarPat(), Dict{Symbol, Symbol}(v.var=>get!(()->gensym(), occMap, occ)))
function preprocess_variables(occ::Vector{Int}, v::CstrPat, occMap::Dict{Vector{Int}, Symbol})
	out = Dict{Symbol, Symbol}()
	out_pats = Pat[]
	for (i,arg) in enumerate(v.args)
		pat, vars = preprocess_variables([occ; i], arg, occMap)
		merge!(out, vars)
		push!(out_pats, pat)
	end
	return (CstrPat(v.cstr, out_pats), out)
end

function preprocess_variables(P::Vector{MatchCase})
	occMap = Dict{Vector{Int}, Symbol}()
	out_vars = Vector{Symbol}[]
	out_pats = Vector{Pat}[]
	out_exprs = Expr[]
	out_callbacks = Symbol[]
	out_callbodies = Expr[]
	for case in P
		patterns = case.patterns
		expr = case.body
		varMap = Dict{Symbol, Symbol}()
		pats = Pat[]
		for (i, pat_elem) in enumerate(patterns)
			pat,vars = preprocess_variables([i], pat_elem, occMap)
			merge!(varMap, vars)
			push!(pats, pat)
		end
		final_expr = Expr(:block, (Expr.(:(=), keys(varMap), values(varMap)))..., expr)
		push!(out_exprs, final_expr)
		push!(out_pats, pats)

		cb_name = gensym()
		cb_vars = collect(values(varMap))
		push!(out_callbacks, cb_name)
		push!(out_callbodies, Expr(:call, cb_name, cb_vars...))
		push!(out_vars, cb_vars)
	end
	return ProcessedPattern.(out_pats, out_callbodies), Callback.(out_callbacks, out_vars, out_exprs), occMap
end

function S(constructors, t, cstr_head, i, P::Vector{ProcessedPattern})
	match_patts = patterns.(P)
	patlen = length(first(match_patts))
	@assert all(l->l==patlen, length.(match_patts))
	arguments = constructors(t)[cstr_head]

	adj_prefix = getindex.(match_patts, (1:(i-1),))
	disc_pat = getindex.(match_patts, i)
	adj_postfix = getindex.(match_patts, (i+1:patlen, ))
	makerows(prefix, c::CstrPat, postfix, p) = 
		if c.cstr == cstr_head
			@assert length(c.args) == length(arguments)
			[ProcessedPattern([prefix; c.args; postfix], p.callback)] 
		else
			ProcessedPattern[]
		end
	makerows(prefix, ::StarPat, postfix, p) = [ProcessedPattern([prefix; repeat([StarPat()], length(arguments)); postfix], p.callback)]
	makerows(prefix, o::OrPat, postfix, p) = [
		S(constructors, t, cstr_head, i, [ProcessedPattern([prefix; o.left; postfix], p.callback)]); 
		S(constructors, t, cstr_head, i, [ProcessedPattern([prefix; o.right; postfix], p.callback)])]
	out = vcat((makerows.(adj_prefix, disc_pat, adj_postfix, P))...)
	return out
end
function D(i, P::Vector{ProcessedPattern})
	makerows(prefix, ::CstrPat, postfix, p) = ProcessedPattern[]
	makerows(prefix, ::StarPat, postfix, p) = [ProcessedPattern([prefix; postfix], p.callback)]
	makerows(prefix, o::OrPat, postfix, p) = [
		D(i, [ProcessedPattern([prefix; o.left; postfix], p.callback)]); 
		D(i, [ProcessedPattern([prefix; o.right; postfix], p.callback)])]

	patlen = length(first(P).patterns)
	orig_patts = patterns.(P)
	adj_prefix = getindex.(orig_patts, (1:(i-1),))
	disc_pattern = getindex.(orig_patts, i)
	adj_postfix = getindex.(orig_patts, (i+1:patlen, ))
	return vcat((makerows.(adj_prefix, disc_pattern, adj_postfix, P))...)
end

collect_binders(pats::Vector{P} where P<:Pat) = collect_binders.(pats)
collect_binders(::StarPat) = nothing

function cc(constructors, o::Vector{Vector{Int}}, P::Vector{ProcessedPattern}, types::Vector{T} where T<:Type) where K
	if length(P) == 0 return Fail() end
	firstpat = first(P)
	if all(iswildcard, firstpat.patterns) return Leaf(firstpat.callback) end
	patterns = getproperty.(P, :patterns)
	i=first(filter((!)∘isnothing, findfirst.((!)∘iswildcard, patterns)))
	elem_type = types[i]
	cstr_heads = reduce(union, heads.(getindex.(patterns, i)); init=Set{Symbol}())
	cstrs = constructors(elem_type)
	possible_heads = keys(cstrs)
	if issubset(possible_heads, cstr_heads) && !issubset(cstr_heads,possible_heads)
		throw(Exception("Invalid head!"))
	end
	switch = Pair{Symbol, DTree}[]
	for head in cstr_heads 
		occs = [o[1:i-1]; vcat.((o[i],), 1:length(cstrs[head])); o[i+1:end]]
		mat = S(constructors, elem_type, head, i, P)
		typs = vcat(types[1:i-1], cstrs[head]..., types[i+1:end])
		case = cc(constructors, occs, mat, typs)
		push!(switch, head => case)
	end
	default = nothing
	if !issetequal(cstr_heads, possible_heads)
		default = cc(constructors, vcat(o[1:i-1], o[i+1:end]), D(i, P), vcat(types[1:i-1], types[i+1:end]))
	end
	return Switch{elem_type}(o[i], switch, default)
end
