
#I discussed only the While function with Luca Omini and Vishnu Arudpiragasam
"""
    lower(e::Exp)

Return a list of stack instructions to evaluate the expression `e`.
For all expressions, the list of instructions should consume values
on the stack and leave a result expression on the stack.

All stack values are integers.
"""
function lower(e)
    @error("lower undefined for $e")
end

function lower(e::Lit)::Vector{Insn}
    # Push the constant on the stack. Convert to an integer first.
    Insn[LDC(Int(e.value))]
end

function lower(e::Block)::Vector{Insn}
    # Empty blocks evaluate to 0.
    if isempty(e.exps)
        return Insn[LDC(0)]
    end

    # Non-empty blocks evaluate to the last expression.
    insns = Insn[]
    for (i, s) in enumerate(e.exps)
        append!(insns, lower(s))

        # Pop all but the last result
        if i < length(e.exps)
            push!(insns, POP())
        end
    end
    insns
end

function lower(e::Bin)::Vector{Insn}
    # Evaluate the left operand, then the right, then perform the operation.
    if e.op == :+
        vcat(lower(e.e1), lower(e.e2), Insn[ADD()])
    elseif e.op == :-
        vcat(lower(e.e1), lower(e.e2), Insn[SUB()])
    elseif e.op == :*
        vcat(lower(e.e1), lower(e.e2), Insn[MUL()])
    elseif e.op == :/
        vcat(lower(e.e1), lower(e.e2), Insn[DIV()])

    # For boolean operators, translate to an `if` and lower.
    elseif e.op in [:(==), :(!=), :<, :<=, :>, :>=]
        lower(If(e, Lit(1), Lit(0)))
    elseif e.op == :&    # &&
        lower(If(e.e1, If(e.e2, Lit(1), Lit(0)), Lit(0)))
    elseif e.op == :|    # ||
        lower(If(e.e1, Lit(1), If(e.e2, Lit(1), Lit(0))))
    else
        @error("unexpected binary expression")
    end
end

function lower(e::Var)::Vector{Insn}
    # Load the variable
    Insn[LD(e.name)]
end

function lower(e::Assign)::Vector{Insn}
    # Dup to leave the RHS on the stack after storing.
    vcat(lower(e.exp), Insn[DUP(), ST(e.name)])
end

function lower(e::Print)::Vector{Insn}
    # Like a block, but print each expression.
    # Leave the last expression on the stack.
    insns = Insn[]
    for (i, s) in enumerate(e.exps)
        append!(insns, lower(s))
        # Dup the last argument so it remains on the stack.
        if i == length(e.exps)
            push!(insns, DUP())
        end
        push!(insns, PRINT())
    end
    insns
end

function lower(e::If)::Vector{Insn}
    t = lower(e.t_part)
    f = lower(e.f_part)

    f_label = gensym("Lfalse")
    j_label = gensym("Ljoin")

    # Sketch of the translation:
    #
    # If(c, t, f)
    #
    # lower c
    # JEQ f_label
    # lower t
    # JMP j_label
    # LABEL f_label
    # lower f
    # LABEL j_label

    if e.cond isa Bin && (e.cond.op in [:(==), :(!=), :(<), :(>), :(<=), :(>=)])
        # If the condition is a binary comparison, generate a conditional jump to the false branch.
        # Subtract and compare the result with 0; that is, (l < r) iff (l - r) < 0.
        # Invert the condition to jump to the false branch. With the subtraction, 0 on the stack
        # means true.

        l = lower(e.cond.e1)
        r = lower(e.cond.e2)

        if e.cond.op == :(==)
            jump = JNE(f_label)
        elseif e.cond.op == :(!=)
            jump = JEQ(f_label)
        elseif e.cond.op == :(<)
            jump = JGE(f_label)
        elseif e.cond.op == :(>)
            jump = JLE(f_label)
        elseif e.cond.op == :(<=)
            jump = JGT(f_label)
        elseif e.cond.op == :(>=)
            jump = JLT(f_label)
        else
            @error("invalid comparison")
        end

        vcat(l,
             r,
             Insn[SUB(), jump],
             t,
             Insn[JMP(j_label), LABEL(f_label)],
             f,
             Insn[LABEL(j_label)],
            )
    elseif e.cond isa Lit && !(e.cond.value == 0 || e.cond.value == false)
        # If the condition is true, just evaluate the true branch.
        t
    elseif e.cond isa Lit && (e.cond.value == 0 || e.cond.value == false)
        # If the condition is false, just evaluate the true branch.
        f
    else
        # For all other conditions, evaluate it and jump to the false branch if 0.
        c = lower(e.cond)
        vcat(c,
             Insn[JEQ(f_label)],
             t,
             Insn[JMP(j_label), LABEL(f_label)],
             f,
             Insn[LABEL(j_label)],
            )
    end
end

function lower(e::While)::Vector{Insn}


    b_label = gensym("Lbottom")
    t_label = gensym("Ltop")


    if e.cond isa Bin && (e.cond.op in [:(==), :(!=), :(<), :(>), :(<=), :(>=)])
        # If the condition is a binary comparison, generate a conditional jump to the false branch.
        # Subtract and compare the result with 0; that is, (l < r) iff (l - r) < 0.
        # Invert the condition to jump to the false branch. With the subtraction, 0 on the stack
        # means true.

        l = lower(e.cond.e1)
        r = lower(e.cond.e2)


        vcat(Insn[LDC(0)],Insn[JMP(b_label)],Insn[LABEL(t_label)],Insn[LDC(1)],Insn[ADD()],lower(e.body),Insn[POP()],Insn[LABEL(b_label)],lower(e.cond),Insn[JNE(t_label)])
    elseif e.cond isa Lit && !(e.cond.value == 0 || e.cond.value == false)
        # If the condition is true, just evaluate the true branch.
        vcat(LDC(0),JMP(b_label),LABEL(t_label),LDC(1),ADD(),lower(e.body),POP(),LABEL(b_label),JMP(t_label))
    elseif e.cond isa Lit && (e.cond.value == 0 || e.cond.value == false)
        vcat(LDC(0))
    else
        # For all other conditions, evaluate it and jump to the false branch if 0.
        vcat(LDC(0),JMP(b_label),LABEL(t_label),LDC(1),ADD(),lower(e.body),POP(),LABEL(b_label),lower(e.cond),JNE(t_label))
    end
end
