"""
    struct State

Interpreter state: program counter, operand stack, variables map, and labels map.
"""
mutable struct State
    pc::Int
    stack::Vector{Int}
    vars::Dict{Symbol,Int}
    labels::Dict{Symbol,Int}

    function State(vars::Dict{Symbol,Int})
        new(1,
            Int64[],
            vars,
            Dict{Symbol,Int64}(),
        )
    end
end

function eval(insns::Vector{Insn}, vars::Dict{Symbol,Int})::Union{Nothing,Tuple{Int,Dict{Symbol,Int}}}
    state = State(copy(vars))

    # Set up the jump labels.
    for (i, insn) in enumerate(insns)
        if insn isa LABEL
            state.labels[insn.label] = i
        end
    end

    while 1 <= state.pc && state.pc <= length(insns)
        println(state)
        insn = insns[state.pc]
        eval_insn(insn, state)
    end

    println("end ", state)

    if isempty(state.stack)
        return nothing
    end

    return (state.stack[end], state.vars)
end

function eval_insn(insn::LD, state)
    # variables are initialized to 0
    v = get(state.vars, insn.name, 0)
    push!(state.stack, v)
    state.pc += 1
end

function eval_insn(insn::ST, state)
    v = pop!(state.stack)
    state.vars[insn.name] = v
    state.pc += 1
end

function eval_insn(insn::LDC, state)
    push!(state.stack, insn.value)
    state.pc += 1
end

function eval_insn(insn::ADD, state)
    y = pop!(state.stack)
    x = pop!(state.stack)
    push!(state.stack, x+y)
    state.pc += 1
end

function eval_insn(insn::SUB, state)
    y = pop!(state.stack)
    x = pop!(state.stack)
    push!(state.stack, x-y)
    state.pc += 1
end

function eval_insn(insn::MUL, state)
    y = pop!(state.stack)
    x = pop!(state.stack)
    push!(state.stack, x*y)
    state.pc += 1
end

function eval_insn(insn::DIV, state)
    y = pop!(state.stack)
    if y == 0
        @error("You can't divide by 0, INF")
    end
    x = pop!(state.stack)
    push!(state.stack, /(x, y))
    state.pc += 1
end

function eval_insn(insn::PRINT, state)
    v = pop!(state.stack)
    println(v)
    state.pc += 1
end

function eval_insn(insn::STOP, state)
    state.pc = 0
end

function eval_insn(insn::POP, state)
    pop!(state.stack)
    state.pc += 1
end

function eval_insn(insn::DUP, state)
    v = state.stack[end]
    push!(state.stack, v)
    state.pc += 1
end

function eval_insn(insn::LABEL, state)
    state.pc += 1
end

function eval_insn(insn::JMP, state)
    state.pc = state.labels[insn.label]
end

function eval_insn(insn::JEQ, state)
    x = pop!(state.stack)
    if x == 0
        state.pc = state.labels[insn.label]
    else
      state.pc+=1
    end
end

function eval_insn(insn::JNE, state)
    x = pop!(state.stack)
    if x != 0
        state.pc = state.labels[insn.label]
    else
      state.pc+=1
    end
end

function eval_insn(insn::JLT, state)
    x = pop!(state.stack)
    if x < 0
        state.pc = state.labels[insn.label]
    else
      state.pc+=1
    end
end

function eval_insn(insn::JGT, state)
    x = pop!(state.stack)
    if x > 0
        state.pc = state.labels[insn.label]
    else
      state.pc+=1
    end
end

function eval_insn(insn::JLE, state)
    x = pop!(state.stack)
    if x <= 0
        state.pc = state.labels[insn.label]
    else
      state.pc+=1
    end
end

function eval_insn(insn::JGE, state)
    x = pop!(state.stack)
    if x >= 0
        state.pc = state.labels[insn.label]
    else
      state.pc+=1
    end
end
