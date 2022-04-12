# Mini-OCaml

For the project, a Mini-OCaml interpreter, a modular design featuring the following components is provided:

• A lexer translating strings into lists of tokens. 

• A parser translating lists of tokens into abstract expressions.

• A type checker computing the type of an expression in an environment.

• An evaluator computing the value of an expression in an environment.

Each of the components can be written and debugged by itself, which is the best one can hope for. 
The glue between the components is provided by constructor types for expressions, types, and tokens. 
There is also a constructor type for the values of Mini-OCaml covering plain and recursive closures.
