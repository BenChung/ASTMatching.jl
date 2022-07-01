abstract type Pat end 
struct StarPat <: Pat end
struct CstrPat <: Pat
	cstr::Symbol
	args::Vector{Pat}
end
struct VarPat <: Pat
	var::Symbol
end
struct OrPat <: Pat
	left::Pat
	right::Pat
end

struct MatchCase
	patterns::Vector{Pat}
	body::Any
end
Base.:(==)(a::MatchCase, b::MatchCase) = all(a.patterns .== b.patterns) && a.body == b.body

iswildcard(::StarPat) = true
iswildcard(::Pat) = false

heads(::StarPat) = Set{Symbol}()
heads(c::CstrPat) = Set([c.cstr])
heads(o::OrPat) = union(heads(o.left), heads(o.right))

Base.:(==)(a::StarPat, b::StarPat) = true
Base.:(==)(a::CstrPat, b::CstrPat) = a.cstr == b.cstr && all(a.args .== b.args)
Base.:(==)(a::VarPat, b::VarPat) = a.var == b.var
Base.:(==)(a::OrPat, b::OrPat) = a.left == b.left && a.right == b.right

extract_pattern(sym::Any) = 
	if sym == :(_)
		StarPat()
	else 
		VarPat(sym)
	end
function extract_pattern(ex::Expr)
	if ex.head == :call
		if ex.args[1] == :(|)
			return OrPat(extract_pattern(ex.args[2]), extract_pattern(ex.args[3]))
		else
			arg_patterns = extract_pattern.(ex.args[2:end])
			nargs = length(arg_patterns)
			return CstrPat(ex.args[1], arg_patterns)
		end
	else
		throw("Invalid match expression $ex") 
	end
end

function extract_case(expr::Expr)
	@assert(expr.head == :call)
	@assert(expr.args[1] == :(=>))
	@assert(length(expr.args) == 3)
	if expr.args[2].head == :tuple 
		exprs = extract_pattern.(expr.args[2].args)
	else
		exprs = Pat[extract_pattern(expr.args[2])]
	end
	term = expr.args[3]
	return MatchCase(exprs, term)
end
function extract_patterns(expr)
	if expr.head == :block
		return MatchCase[extract_case(t) for t in expr.args if t isa Expr]
	elseif expr.head == :call && expr.args[1] == :(=>)
		return MatchCase[extract_case(expr)]
	end
end
