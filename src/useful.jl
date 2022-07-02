specialize_matrix(constructors, typ, head::Symbol, mat::Vector{Vector{Pat}}) = vcat((specialize_row.(constructors, typ, head, mat))...)
specialize_row(constructors, typ, head::Symbol, row::Vector{Pat})::Vector{Vector{Pat}} = specialize_row(constructors, typ, head, first(row), row[2:end])
specialize_row(constructors, typ, head::Symbol, pat::CstrPat, rest)::Vector{Vector{Pat}} = 
	if head == pat.cstr 
		[Pat[pat.args; rest]] 
	else [] 
	end
specialize_row(constructors, typ, head::Symbol, pat::StarPat, rest)::Vector{Vector{Pat}} = [Pat[repeat([StarPat()], length(constructors(typ)[head])); rest]]
specialize_row(constructors, typ, head::Symbol, pat::OrPat, rest)::Vector{Vector{Pat}} = 
	[specialize_row(constructors, typ, head, pat.left, rest); 
	 specialize_row(constructors, typ, head, pat.right, rest)]

specialize_vect(constructors, typ, head::Symbol, vect::Vector{Pat}) = specialize_vect(constructors, typ, head, first(vect), vect[2:end])
specialize_vect(constructors, typ, head::Symbol, pat::CstrPat, rest) = [pat.args; rest]
specialize_vect(constructors, typ, head::Symbol, pat::StarPat, rest) = Pat[repeat([StarPat()], length(constructors(typ)[head])); rest]


specialize_tyvect(constructors, typ, head::Symbol, tvs::Vector{Type}) = Type[constructors(typ)[head]; tvs[2:end]]

default_mat(mat::Vector{Vector{Pat}})::Vector{Vector{Pat}}  = vcat((default_mat.(mat))...)
default_mat(row::Vector{Pat})::Vector{Vector{Pat}} = default_mat(first(row), row)
default_mat(pat::CstrPat, row)::Vector{Vector{Pat}} = []
default_mat(pat::StarPat, row)::Vector{Vector{Pat}} = [row[2:end]]
default_mat(pat::OrPat, row)::Vector{Vector{Pat}} = [default_mat(pat.left, row); default_mat(pat.right, row)]

function useful(constructors, P::Vector{Vector{Pat}}, q::Vector{Pat}, ts::Vector{Type})
	if length(q) == 0
		return length(P) == 0
	end
	return useful(constructors, first(ts), P, first(q), q, ts)
end
useful(constructors, typ, P::Vector{Vector{Pat}}, h::CstrPat, q::Vector{Pat}, ts::Vector{Type}) = 
	useful(typ, 
		specialize_matrix(constructors, typ, h.cstr, P), 
		specialize_vect(constructors, typ, h.cstr, q), 
		specialize_tyvect(constructors, typ, h.cstr, ts))
function useful(constructors, typ, P::Vector{Vector{Pat}}, h::StarPat, q::Vector{Pat}, ts::Vector{Type}) 
	matched_heads = reduce(union, heads.(first.(P)); init=Set{Symbol}())
	if hasmethod(constructors, Tuple{Type{typ}}) && begin all_heads = keys(constructors(typ)); issetequal(matched_heads, all_heads) end 
		for head in all_heads
			specmat = specialize_matrix(constructors, typ, head, P)
			specvect = specialize_vect(constructors, typ, head, q)
			if useful(constructors, 
				specmat, specvect, 
				specialize_tyvect(constructors, typ, head, ts))
				return true
			end
		end
		return false
	else 
		dm = default_mat(P)
		disc = q[2:end]
		return useful(constructors, dm, disc, ts[2:end])
	end
end
useful(constructors, typ, P::Vector{Vector{Pat}}, h::OrPat, q::Vector{Pat}, ts::Vector{Type}) = useful(P, [h.left;q[2:end]], ts) || useful(P, [h.right;q[2:end]], ts)

abstract type CounterPat end
struct StarCounterPat <: CounterPat
	typ::Type
end
struct CstrCounterPat <: CounterPat
	cstr::Symbol
	args::Vector{CounterPat}
	typ::Type
end
Base.:(==)(a::StarCounterPat, b::StarCounterPat) = a.typ == b.typ
Base.:(==)(a::CstrCounterPat, b::CstrCounterPat) = a.cstr == b.cstr && all(a.args .== b.args) && a.typ == b.typ
function Base.show(io::IO, x::StarCounterPat) 
	print(io, "_::")
	Base.show(io, x.typ)
end
function Base.show(io::IO, x::CstrCounterPat)
	print(io, "$(x.cstr)(")
	if length(x.args) > 0
		for el in x.args[1:end-1]
			show(io, el)
			print(io, ", ")
		end
		show(io, x.args[end])
	end
	print(io, ")")
end
struct EmptyPat end

counterexample(constructors, P::Vector{Vector{Pat}}, ts::Vector{Type}) = counterexample(constructors, P, ts, length(ts))
function counterexample(constructors, P::Vector{Vector{Pat}}, ts::Vector{Type}, n::Int)::Union{Vector{CounterPat}, EmptyPat}
	if n == 0
		if length(P) == 0 return CounterPat[] end
		if length(first(P)) == 0 return EmptyPat() end
	end

	typ = first(ts)
	matched_heads = reduce(union, heads.(first.(P)); init=Set{Symbol}())
	if hasmethod(constructors, Tuple{Type{typ}}) && begin all_heads = keys(constructors(typ)); issetequal(matched_heads, all_heads) end 
		# it is a complete signature
		for head in all_heads
			nhead = length(constructors(typ)[head])
			specmat = specialize_matrix(constructors, typ, head, P)
			rec = counterexample(constructors, specmat, 
				specialize_tyvect(constructors, typ, head, ts), 
				nhead + n - 1)
			if !(rec isa EmptyPat)
				return CounterPat[CstrCounterPat(head, rec[1:nhead], typ); rec[nhead+1:end]]
			end
		end
		return EmptyPat()
	else
		rec = counterexample(constructors, default_mat(P), ts[2:end], n-1)
		if rec isa EmptyPat
			return EmptyPat()
		end
		if isempty(matched_heads) || !hasmethod(constructors, Tuple{Type{typ}})
			return [StarCounterPat(typ); rec]
		else
			example_head = first(setdiff(Set(all_heads), matched_heads))
			ex = constructors(typ)[example_head]
			return [CstrCounterPat(example_head, [StarCounterPat(t) for t in ex], typ); rec[2:end]]
		end
	end
end
