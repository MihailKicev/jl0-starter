# Implementing an interpreter for JL0

In this assignment, you will implement an interpreter for a small subset of Julia, called JL0.

The interpreter is implemented as a translation from Julia expressions into abstract syntax trees
and then into a simple bytecode, which is evaluated using an operand stack.

## Getting started

Install Julia: `http://julialang.org`.

Run `julia main.jl` to get the JL0 REPL.

If you type an expression in the REPL, you should see some information on how it is parsed,
how it is lowered, and how it is evaluated on the stack machine.
The final thing it prints is the result.

You can type `:q` into the REPL to quit.

## Language description

JL0 is a small subset of Julia.

It has the following features:

- integer arithmetic, including constants, `+`, `-`, `*`, and `/`
- booleans, including constants, `&&`, `||`, and `!`
- variables and assignment
- `if` expressions (and also conditional `?:` expressions)
- `while` expressions
- `begin` blocks
- `print` expressions

The syntax is identical to Julia's. Indeed the interpreter just uses Julia
parser to parse expressions.

The semantics differ in that only integers are supported. Booleans are
translated into the integers 0 and 1.  For instance `print true` will print `1`,
not `true`. The division operator `/` performs integer division (implemented as
`div` in Julia).

In addition, while loops evaluate to an integer (the loop iteration count, rather than to `nothing`).

## Implementation

The Julia parser is used to parse single lines of code entered into a REPL
(`repl.jl`), which are translated and evaluated as described below.

The code is parsed as a Julia `Expr`. This is translated (`parse.jl`) into a
simpler abstract syntax tree (`syntax.jl`).

The AST is translated (`lower.jl`) into a vector of instructions (`insns.jl`).

Instructions are executed by the evaluator (`eval.jl`), which implements a
simple abstract machine.

## Bytecode

The abstract machine state consists of:

- a sequence of instructions
- a program counter: this is the index of the instruction being executed
- an operand stack: integers and pushed onto the stack and popped to evaluate expressions
- a dictionary mapping variable names to values
- a dictionary mapping label names to instruction indices

The following bytecode instructions are supports. See `insns.jl` for details.

- `LDC n` - push a constant on the stack
- `LD x` - push the local variable on the stack
- `ST x` - pop the stack and store into the given variable
- `ADD` - pop two values and push their sum
- `SUB` - pop two values and push their difference
- `MUL` - pop two values and push their product
- `DIV` - pop two values and push the lower divided by the upper
- `DUP` - duplicate: push the top value again
- `POP` - pop the top value and discard it
- `LABEL L` - a jump target label named `L`
- `JMP L` - jump to label `L`
- `JEQ L` - pop the stack and jump to `L` if `== 0`
- `JNE L` - pop the stack and jump to `L` if `!= 0`
- `JLT L` - pop the stack and jump to `L` if `< 0`
- `JGT L` - pop the stack and jump to `L` if `> 0`
- `JLE L` - pop the stack and jump to `L` if `<= 0`
- `JGE L` - pop the stack and jump to `L` if `>= 0`
- `STOP` - stop the program

## Assignment

Various parts of this implementation are incomplete. Your task is to complete
the implementation.

1. Evaluation is not implemented for `-`, `*`, and `/`.

2. Lowering is not implemented for `while` loops, `&&`, and `||`. These cases should be added to `lower.jl`

3. Evaluation is not implemented for conditional jumps, for arithmetic operators, and for `Block` statements.
These cases should be added to `eval.jl`.

## Evaluation of arithmetic.

Just follow the example of `+`. Pop two operands, perform the operation and push the result.
Be careful of the ordering of the operands!

## Lowering `&&` and `||`

The simplest way to lower these operators is to translate them into an `If` and use the lowering for `If`.

`e1 && e2` is equivalent to `e1 ? e2 : false`

`e1 || e2` is equivalent to `e1 ? true : e2`

## Lowering `While`

First study how `If` expressions are lowered.

To lower a while loop, you need to create a label for the top of the loop and the bottom of the loop.

A simple translation is:

    while c
       s

    -->

    JMP Lbottom
    LABEL Ltop
    lower(s)
    POP            ; s leaves a value on the stack, so need to pop it
    LABEL Lbottom
    lower(c)
    JNE Ltop

This lowering should work for any condition, but it's better to handle binary comparison expressions (e.g., `<` or `==`) specially.
You can handle `true` and `false` conditions specially as well.

An extra complication is that the loop iteration count needs to be tracked.
One can do this by pushing 0 on the stack before the loop, then incrementing the value on top of the stack
before each loop body. This should leave the iteration count on top of the stack when the loop exits.

## Evaluating conditional jumps

Implement the evaluation cases for `JEQ`, `JNE`, `JLT`, etc. in `eval.jl`.
