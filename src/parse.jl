
function parse(x::AbstractString)::Union{Exp,Nothing}
    try
        expr = Base.parse_input_line(x)
        println(expr)
        if expr isa Expr || expr isa Symbol
            parse(expr)
        else
            nothing
        end
    catch ex
        nothing
    end
end

function parse(x::Symbol)::Union{Exp,Nothing}
    if x == :true
        return Lit(1)
    elseif x == :false
        return Lit(0)
    else
        return Var(x)
    end
end

function parse(x::Int)::Union{Exp,Nothing}
    return Lit(x)
end

function parse(x::Bool)::Union{Exp,Nothing}
    return Lit(x)
end

function parse(e)::Union{Exp,Nothing}
    @error("syntax error: unexpected expression $e")
    return nothing
end

function parse(e::Expr)::Union{Exp,Nothing}
    if e.head == :toplevel
        args = filter(x -> !(x isa LineNumberNode), e.args)
        if length(args) == 1
            parse(args[1])
        else
            Block(map(parse, args))
        end
    elseif e.head == :call
        if length(e.args) > 2 && e.args[1] in [:+, :-, :*, :/, :<, :<=, :>, :>=, :(==), :(!=), :&, :|]
            return foldl((x, y) -> Bin(e.args[1], x, y), map(parse, e.args[3:end]); init=parse(e.args[2]))
        elseif length(e.args) >= 1 && e.args[1] == :print
            return Print(map(parse, e.args[2:end]))
        elseif length(e.args) == 2 && e.args[1] == :!
            return If(parse(e.args[2]), Lit(false), Lit(true))
        elseif length(e.args) == 2 && e.args[1] == :-
            return Bin(:-, Lit(0), e.args[2])
        else
            @error("syntax error: unexpected expression $e")
        end
    elseif e.head == :if
        if length(e.args) == 3
            return If(parse(e.args[1]), parse(e.args[2]), parse(e.args[3]))
        elseif length(e.args) == 2
            return If(parse(e.args[1]), parse(e.args[2]), Block(Exp[]))
        end
    elseif e.head == :while
        return While(parse(e.args[1]), parse(e.args[2]))
    elseif e.head == :block
        args = filter(x -> !(x isa LineNumberNode), e.args)
        if length(args) == 1
            return parse(args[1])
        else
            return Block(map(parse, args))
        end
    elseif e.head == :(=) && e.args[1] isa Symbol && length(e.args) == 2
        return Assign(e.args[1], parse(e.args[2]))
    else
        @error("syntax error: unexpected expression $e")
        nothing
    end
end
