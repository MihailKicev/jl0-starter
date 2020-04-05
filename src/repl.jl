function prompt()
    print("J0> ")
end

function repl()
    println("Welcome to J0. Enter expressionx and watch them get evaluated! Type `:q` to quit.")
    prompt()

    vars = Dict{Symbol,Int}()

    while !eof(stdin)
        line = readline()

        if line == ":q" || line == ":quit"
            println("Bye!")
            break
        end

        if line == ""
            prompt()
            continue
        end

        println("read $line")

        e = parse(line)
        println("parsed $e")

        if e == nothing
            println("syntax error")
        else
            insns = lower(e)
            println("lowered $insns")

            (v, vars) = eval(insns, vars)

            v != nothing && println(v)
        end

        prompt()
    end
end
