abstract type Insn end

# Load a local variable: push its value on the stack
struct LD <: Insn
    name::Symbol
end

# Store a local variable: pop its value from the stack and store
struct ST <: Insn
    name::Symbol
end

# Push a constant on the stack
struct LDC <: Insn
    value::Int64
end

# Arithmetic operators. Pop two operands and push result.
struct ADD <: Insn end
struct SUB <: Insn end
struct MUL <: Insn end
struct DIV <: Insn end

# Pop and print the value on top of the stack
struct PRINT <: Insn end

# Stop the program
struct STOP <: Insn end

# Pop the value on top of the stack and discard it
struct POP <: Insn end

# Duplicate the value on top of the stack (i.e., push it again)
struct DUP <: Insn end

# Jump target label. No stack changes.
struct LABEL <: Insn
    label::Symbol
end

# Unconditional jump. Jump to the given label. No stack changes.
struct JMP <: Insn
    label::Symbol
end

# Conditional jumps.
# Pop and jump to the given label if == 0.
struct JEQ <: Insn
    label::Symbol
end

# Pop and jump to the given label if != 0.
struct JNE <: Insn
    label::Symbol
end

# Pop and jump to the given label if < 0.
struct JLT <: Insn
    label::Symbol
end

# Pop and jump to the given label if > 0.
struct JGT <: Insn
    label::Symbol
end

# Pop and jump to the given label if <= 0.
struct JLE <: Insn
    label::Symbol
end

# Pop and jump to the given label if >= 0.
struct JGE <: Insn
    label::Symbol
end
