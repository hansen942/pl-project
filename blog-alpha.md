# An ML-style Functional Language
## Vision 
The goal of the project is to build a small ml-style functional language implementing a typed language that supports type inference, polymorphism, recursion, etc.
Some other cool features I am thinking of adding include Haskell-style functors and monad syntax (maybe do notation).
## Status
During this sprint, my understanding of type-inference was limited, so I have so far implemented an extension of the applied lambda calculus that supports integers, booleans, print statements, common operations, fixed points operators (using let rec notation), and this is all type checked under a simply-typed-esque type system (it is not exactly simply typed because we allow fixed-points; I got around this by making fixed points hidden from the type checkers perspective by putting this into the let rec expressions and only translating it down to an actual fixed-point operator after type checking).
I do not currently have a lexer or parser, but by writing out the AST I can type check and run small programs like a factorial function.
## Next Steps
With less work over break, I expect to be able to start implementing type inference and recursive types soon.


