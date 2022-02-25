

compile(l::Leaf{K}, var_map::Dict{Vector{Int}, Symbol}) where K = l.term
compile(::Fail{K}, var_map::Dict{Vector{Int}, Symbol}) where K = 
		:(throw(Exception("Pattern matching failed!")))
function compile(s::Switch{K, T}, var_map::Dict{Vector{Int}, Symbol}) where {K,T}
	cases = s.cases
	cstrs = constructors(T)
	cstr_keys = constructor_keys(T)
	occ = s.occ
	function make_conditional(case_idx)
		println(var_map[occ])
		# condition
		cond = :(headof($(var_map[occ])) == $(cstr_keys[first(cases[case_idx])]))
		# body
		body = :(begin end)
		arity = length(cstrs[first(cases[case_idx])])
		for i = 1:arity
			var=get!(()->gensym(), var_map, [occ; i])
			push!(body.args, :($var = argof($(var_map[occ]), $i)))
		end
		push!(body.args, compile(last(cases[case_idx]), var_map))
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
		push!(expr.args, compile(s.default, var_map))
	end
	return expr
end
function toplevel_compile(t::DTree{K}, inputs::Vector{T}, var_map::Dict{Vector{Int}, Symbol}) where {T,K}
	out = :(begin end)
	for i=1:length(inputs)
		var = get!(()->gensym(), var_map, [i])
		push!(out.args, :($var = $(inputs[i])))
	end
	push!(out.args, compile(t, var_map))
	return out
end