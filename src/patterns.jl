abstract type Pat end 
const TyPat = Type{T} where T<:Pat
struct StarPat <: Pat end
struct CstrPat{C, N, A<:Tuple{Vararg{<:Pat, N}}} <: Pat end
struct VarPat{S} <: Pat end
struct OrPat{P1<:Pat, P2<:Pat} end

iswildcard(::Type{StarPat}) = true
iswildcard(::Type{<:Pat}) = false

heads(::Type{StarPat}) where K = Set{Symbol}()
heads(::Type{CstrPat{C, N, A}}) where {C,N,A} = Set([C])
heads(::Type{OrPat{P1, P2}}) where {P1,P2} = union(heads(P1), heads(P2))

extract_pattern(sym::Symbol) = 
	if sym == :(_)
		StarPat
	else 
		VarPat{sym}
	end
function extract_pattern(ex::Expr)
	if ex.head == :call
		if ex.args[1] == :(|)
			return OrPat{extract_pattern(ex.args[2]), extract_pattern(ex.args[3])}
		else
			arg_patterns = extract_pattern.(ex.args[2:end])
			nargs = length(arg_patterns)
			return CstrPat{ex.args[1], nargs, Tuple{arg_patterns...}}
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
		exprs = (Type{P} where P<:Pat)[extract_pattern(expr.args[2])]
	end
	term = expr.args[3]
	return Pair{Type{PS} where PS<:Tuple{Vararg{P where P<:Pat}}, Any}(Tuple{exprs...}, term)
end
function extract_patterns(expr)
	if expr.head == :block
		return Pair{Type{PS} where PS<:Tuple{Vararg{P where P<:Pat}}, Any}[extract_case(t) for t in expr.args if t isa Expr]
	elseif expr.head == :call && expr.args[1] == :(=>)
		return Pair{Type{PS} where PS<:Tuple{Vararg{P where P<:Pat}}, Any}[extract_case(expr)]
	end
end
