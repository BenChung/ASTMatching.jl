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

abstract type Arity end
struct Expanding <: Arity 
	fixed::Int
end
struct Fixed <: Arity
	fixed::Int
end

struct Switch{T} <: DTree
	occ::Vector{Int}
	cases::Vector{Pair{Tuple{Symbol, Arity}, DTree}}
	default::Union{DTree, Nothing}
end

abstract type Occurrence end
struct Index <: Occurrence
       ind::Int
end
struct Star <: Occurrence
       start::Int
end
Base.isless(i1::Index, i2::Index) = i1.ind < i2.ind
Base.isless(i1::Index, i2::Star) = i1.ind < i2.start
Base.isless(i1::Star, i2::Index) = i1.start < i2.ind
Base.isless(i1::Star, i2::Star) = i1.start < i2.start


Base.:(==)(a::Leaf, b::Leaf) = a.term == b.term
Base.:(==)(a::Fail, b::Fail) = true
Base.:(==)(a::Switch{T}, b::Switch{T}) where T = a.occ == b.occ && a.cases == b.cases && a.default == b.default
function get!(f, t::Trie{Occurrence, T}, key) where T
       if haskey(t, key)
               val = get(t[key...])
               if !ismissing(val)
                       return val
               end
       end
       nv = f()
       setindex!(t, nv, key...)
       return nv
end
preprocess_variables(occ::Vector{Int}, p::StarPat, occMap::Trie{Occurrence, Symbol}) = (p, Dict{Symbol, Symbol}())
preprocess_variables(occ::Vector{Int}, p::MultiStarPat, occMap::Trie{Occurrence, Symbol}) = (p, Dict{Symbol, Symbol}())
preprocess_variables(occ::Vector{Int}, v::MultiVarPat, occMap::Trie{Occurrence, Symbol}) = (MultiStarPat(), Dict{Symbol, Symbol}(v.var=>get!(()->gensym(), occMap, [map(Index, occ[1:end-1]); Star(occ[end])])))
preprocess_variables(occ::Vector{Int}, v::VarPat, occMap::Trie{Occurrence, Symbol}) = (StarPat(), Dict{Symbol, Symbol}(v.var=>get!(()->gensym(), occMap, map(Index, occ))))
function preprocess_variables(occ::Vector{Int}, v::CstrPat, occMap::Trie{Occurrence, Symbol})
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
	occMap = Trie{Occurrence, Symbol}()
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
			pat,vars = preprocess_variables(Int[i], pat_elem, occMap)
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

function arg_pats(ts, arity::Expanding)
	args = Pat[]
	for t in ts 
		if t <: Type{<:AbstractArray}
			for i=1:arity.fixed
				push!(args, StarPat())
			end
			push!(args, MultiStarPat())
		else
			push!(args, StarPat())
		end
	end
	return args
end
function arg_pats(ts, arity::Fixed)
	args = Pat[]
	for t in ts 
		if t <: Type{<:AbstractArray}
			for i=1:arity.fixed
				push!(args, StarPat())
			end
		else
			push!(args, StarPat())
		end
	end
	return args
end
arg_pats(ts) = map(arg_pat, ts)
arg_pat(::Type{<:AbstractArray}) = MultiStarPat()
arg_pat(::Any) = StarPat()

function consistent_arity(args, arity::Fixed) 
	satisfying = arity.fixed
	for arg in args
		if arg isa StarPat || arg isa CstrPat
			satisfying -= 1
		elseif arg isa MultiStarPat
			satisfying = 0
			break
		end
	end
	return satisfying == 0
end
function consistent_arity(args, arity::Expanding) 
	satisfying = arity.fixed
	for arg in args
		if arg isa StarPat || arg isa CstrPat
			satisfying -= 1
		elseif arg isa MultiStarPat
			return satisfying >= 0
		end
	end
	return false
end

split_patts(P, i, patlen) = (getindex.(P, (1:(i-1),)), getindex.(P, i), getindex.(P, (i+1:patlen, )))
function S(constructors, t, cstr_head, arity, i, P::Vector{ProcessedPattern})
	match_patts = patterns.(P)
	patlen = length(first(match_patts))
	#@assert all(l->l==patlen, length.(match_patts))
	arguments = constructors(t)[cstr_head]

    cstr_pats = arg_pats(arguments, arity)
    adj_prefix, disc_pat, adj_postfix = split_patts(match_patts, i, patlen)
	makerows(prefix, c::CstrPat, postfix, p) = 
		if c.cstr == cstr_head && consistent_arity(c.args, arity)
			#@assert length(c.args) == length(arguments)
			[ProcessedPattern([prefix; c.args; postfix], p.callback)] 
		else
			ProcessedPattern[]
		end
	makerows(prefix, ::StarPat, postfix, p) = [ProcessedPattern([prefix; cstr_pats; postfix], p.callback)]
	makerows(prefix, ::MultiStarPat, postfix, p) = [ProcessedPattern([prefix; cstr_pats; MultiStarPat(); postfix], p.callback)]
	makerows(prefix, o::OrPat, postfix, p) = [
		S(constructors, t, cstr_head, arity, i, [ProcessedPattern([prefix; o.left; postfix], p.callback)]); 
		S(constructors, t, cstr_head, arity, i, [ProcessedPattern([prefix; o.right; postfix], p.callback)])]
	out = vcat((makerows.(adj_prefix, disc_pat, adj_postfix, P))...)
	return out
end
function Dsingle(i, P::Vector{ProcessedPattern})
	makerows(prefix, ::CstrPat, postfix, p) = ProcessedPattern[]
	makerows(prefix, ::StarPat, postfix, p) = [ProcessedPattern([prefix; postfix], p.callback)]
    makerows(prefix, ::MultiStarPat, postfix, p) = [ProcessedPattern([prefix; MultiStarPat(); postfix], p.callback)]
    makerows(prefix, o::OrPat, postfix, p) = [
            Dsingle(i, [ProcessedPattern([prefix; o.left; postfix], p.callback)]);
            Dsingle(i, [ProcessedPattern([prefix; o.right; postfix], p.callback)])]

    patlen = length(first(P).patterns)
    orig_patts = patterns.(P)
    adj_prefix, disc_pat, adj_postfix = split_patts(orig_patts, i, patlen)
    if all(x->x isa MultiStarPat, disc_pat)
    	return map((a,b)->[a; b], adj_prefix, adj_postfix)
    end
    return vcat((makerows.(adj_prefix, disc_pat, adj_postfix, P))...)
end

collect_binders(pats::Vector{P} where P<:Pat) = collect_binders.(pats)
collect_binders(::StarPat) = nothing

collect_arities(pats::Vector{ProcessedPattern}, i, c, n) = filter(x->!isnothing(x), collect_arity.(pats, i, c, n))
collect_arity(pat::ProcessedPattern, i, c, n) = collect_arity(pat.patterns[i], c, n)
collect_arity(cstrPat::CstrPat, c, n) = if cstrPat.cstr == c arity(cstrPat.args, n) else nothing end
collect_arity(p, c, n) = nothing
function arity(ps::Vector{Pat}, n)
	if any(x->x isa MultiStarPat, ps) 
		Expanding(length(ps)-1-n) 
	else 
		Fixed(length(ps)-n)
	end
end

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
	switch = Pair{Tuple{Symbol, Arity}, DTree}[]
	for head in cstr_heads
		head_typing = cstrs[head]
		if any(x-> x <: AbstractArray, head_typing)
			arities = collect_arities(P, i, head, length(head_typing)-1)
		else 
			arities = [Fixed(length(head_typing))]
		end

		occs = [o[1:i-1]; vcat.((o[i],), 1:length(head_typing)); o[i+1:end]]
		for arity in arities
			mat = S(constructors, elem_type, head, arity, i, P)
			typs = vcat(types[1:i-1], head_typing..., types[i+1:end])
			case = cc(constructors, occs, mat, typs)
			push!(switch, (head, arity) => case)
		end
	end
	default = nothing
	if !issetequal(cstr_heads, possible_heads)
		default = cc(constructors, vcat(o[1:i-1], o[i+1:end]), Dsingle(i, P), vcat(types[1:i-1], types[i+1:end]))
	end
	res = Switch{elem_type}(o[i], switch, default)
	return res
end
