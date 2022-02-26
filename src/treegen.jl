abstract type DTree{K} end
struct Leaf{K} <: DTree{K}
	term::Any
end
struct Fail{K} <: DTree{K} end

struct Switch{K, T} <: DTree{K}
	occ::Vector{Int}
	cases::Vector{Pair{K, DTree{K}}}
	default::Union{DTree{K}, Nothing}
end

const MatchMatrix{K} = Vector{Pair{V, T}} where {P<:Pat, V<:Vector{P}, T}

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

function preprocess_variables(P::Vector{Vector{Pat}}, A::Vector{T}) where {T}
	occMap = Dict{Vector{Int}, Symbol}()
	out_pats = Vector{Pat}[]
	out_exprs = Expr[]
	for (pattern, expr) in zip(P, A)
		varMap = Dict{Symbol, Symbol}()
		pats = Pat[]
		for (i, pat_elem) in enumerate(pattern)
			pat,vars = preprocess_variables([i], pat_elem, occMap)
			merge!(varMap, vars)
			push!(pats, pat)
		end
		final_expr = Expr(:block, (Expr.(:(=), keys(varMap), values(varMap)))..., expr)
		push!(out_exprs, final_expr)
		push!(out_pats, pats)
	end
	return out_pats, out_exprs, occMap
end
function preprocess_variables(P::Vector{Pair{Vector{Pat}, T}}) where {T}
	pats, exprs, occMap = preprocess_variables(first.(P), last.(P))
	return Pair.(pats, exprs), occMap
end

function S(constructors, t, cstr_head, i, P::Vector{Vector{Pat}}, A::Vector{T}) where {T}
	rowty = Pair{Vector{Pat}, T}
	patlen = length(first(P))
	@assert all(l->l==patlen, length.(P))
	@assert length(P) == length(A)
	arguments = constructors(t)[cstr_head]

	adj_prefix = getindex.(P, (1:(i-1),))
	patterns = getindex.(P, i)
	adj_postfix = getindex.(P, (i+1:patlen, ))
	makerows(prefix, c::CstrPat, postfix, a) = 
		if c.cstr == cstr_head
			@assert length(c.args) == length(arguments)
			[[prefix; c.args; postfix] => a] 
		else
			rowty[]
		end
	makerows(prefix, ::StarPat, postfix, a) = rowty[[prefix; repeat([StarPat()], length(arguments)); postfix] => a]
	makerows(prefix, o::OrPat, postfix, a) = [S(constructors, t, cstr_head, i, [[prefix; o.left; postfix]], [a]); S(constructors, t, cstr_head, i, [[prefix; o.right; postfix]], [a])]
	out = vcat((makerows.(adj_prefix, patterns, adj_postfix, A))...)
	return out
end
function D(i, P::Vector{Vector{Pat}}, A::Vector{T}) where {T}
	rowty = Pair{Vector{Pat{K}}, T}
	makerows(prefix, ::CstrPat, postfix, a) = rowty[]
	makerows(prefix, ::StarPat, postfix, a) = rowty[[prefix; postfix] => a]
	makerows(prefix, o::OrPat, postfix, a) = [D([[prefix; o.left; postfix]], a); D([[prefix; o.right; postfix]], a)]

	patlen = length(first(P))
	patterns = getindex.(P, i)
	adj_prefix = getindex.(P, (1:(i-1),))
	patterns = getindex.(P, i)
	adj_postfix = getindex.(P, (i+1:patlen, ))
	return vcat((makerows.(adj_prefix, patterns, adj_postfix, A))...)
end

collect_binders(pats::Vector{P} where P<:Pat) = collect_binders.(pats)
collect_binders(::StarPat) = nothing
function cc(o::Vector{Vector{Int}}, P::MatchMatrix{K}, types::Vector{T} where T<:Type) where K
	if length(P) == 0 return Fail{K}() end
	firstpat = first(P)
	if all(iswildcard, first(firstpat)) return Leaf{K}(last(firstpat)) end

	i=first(filter((!)∘isnothing, findfirst.((!)∘iswildcard, first.(P))))
	elem_type = types[i]
	cstr_heads = reduce(union, heads.(getindex.(first.(P), i)); init=Set{K}())
	cstrs = constructors(elem_type)
	possible_heads = keys(cstrs)
	if issubset(possible_heads, cstr_heads) && !issubset(cstr_heads,possible_heads)
		throw(Exception("Invalid head!"))
	end

	Pats = first.(P)
	A = last.(P)
	switch = Pair{K, DTree{K}}[head => cc([o[1:i-1]; vcat.((o[i],), 1:length(cstrs[head])); o[i+1:end]], S(elem_type, head, i, Pats, A), vcat(types[1:i-1], cstrs[head]..., types[i+1:end])) for head in cstr_heads]
	default = nothing
	println(cstr_heads)
	println(possible_heads)
	if !issetequal(cstr_heads, possible_heads)
		default = cc(vcat(o[1:i-1], o[i+1:end]), D(i, Pats, A), vcat(types[1:i-1], types[i+1:end]))
	end
	return Switch{K, elem_type}(o[i], switch, default)
end
