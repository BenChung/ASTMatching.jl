compile(constructor_keys, constructors, l::Leaf, var_map::Trie{Occurrence, Symbol}) = l.term
compile(constructor_keys, constructors, ::Fail, var_map::Trie{Occurrence, Symbol}) =
		:(throw(Exception("Pattern matching failed!")))

true_arity(base, vararg_arity::Fixed) = base + vararg_arity.fixed
true_arity(base, vararg_arity::Expanding) = base + vararg_arity.fixed
function compile(constructor_keys, constructors, s::Switch{T}, var_map::Trie{Occurrence, Symbol}) where {T}
	cases = s.cases
	cstrs = constructors(T)
	cstr_keys = constructor_keys(T)
	occ = map(Index, s.occ)
	arity_check(expr, arity::Expanding) = :($expr <= $(arity.fixed))
	arity_check(expr, arity::Fixed) = :($expr == $(arity.fixed))
	function make_conditional(case_idx)
		# condition
		case = cases[case_idx]
		head = first(first(case))
		arity = last(first(case))
		structure = get(var_map[occ...])
		cond = :(headof($T, $(structure)) == $(QuoteNode(cstr_keys[head])) && $(arity_check(:(length(args($T, $(structure)))), arity)))
		# body
		body = :(begin end)
		real_arity = true_arity(length(cstrs[head])-1, arity)
		paths = map(c->last(Tries.path(c))=>get(c), children(var_map[occ...]))
		for (idx, var) in filter(p->p[1] isa Index, paths)
			if idx.ind > real_arity
				continue
			end
			push!(body.args, :($var = argof($T, $(get(var_map[occ...])), $(idx.ind))))
		end
		for (star, var) in filter(p->p[1] isa Star, paths)
			push!(body.args, :($var = args($T, $(get(var_map[occ...])))[($(star.start)):end]))
		end
		push!(body.args, compile(constructor_keys, constructors, last(case), var_map))
		return cond, body
	end

	expr = :(begin end)
	if length(cases) > 0
		out_expr = Expr(:if)
		cond,body = make_conditional(1)
		push!(out_expr.args, cond)
		push!(out_expr.args, body)
		curr_expr = out_expr
		caseno = 2
		while caseno <= length(cases)
			next_expr = Expr(:elseif)
			push!(curr_expr.args, next_expr)
			cond,body = make_conditional(caseno)
			push!(next_expr.args, cond)
			push!(next_expr.args, body)
			curr_expr = next_expr
			caseno += 1
		end
		expr = out_expr
	end
	if !isnothing(s.default)
		push!(expr.args, compile(constructor_keys, constructors, s.default, var_map))
	end
	return expr
end
function toplevel_compile(constructor_keys, constructors, t::DTree, inputs::Vector{T}, var_map::Trie{Occurrence, Symbol}) where {T}
	out = :(begin end)
	for i=1:length(inputs)
		var = get!(()->gensym(), var_map, [Index(i)])
		push!(out.args, :($var = $(inputs[i])))
	end
	push!(out.args, compile(constructor_keys, constructors, t, var_map))
	return out
end