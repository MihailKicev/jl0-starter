using Pkg

Pkg.activate(".")
Pkg.build()

using JL0

JL0.repl()
