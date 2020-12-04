# A Small Functional Language
The goal of the project is to build a small ml-like functional language that is strongly typed and supports type inference, polymorphism, recursion, etc.
It also has limited support for type classes.

## Status
The language is based off the applied lambda calculus extended with let statements.
It also supports user defined algebraic data types, prenex polymorphism type inference, and I am working to add type classes.

Currently the only typeclass is `printable` of types that can be printed with the built-in print function.
It is currently not possible for the user to define typeclasses, and after thinking about how this could be accomplished, I have decided that while I intend to add more typeclasses, I probably will not allow users to define typeclasses themselves.

## How to Build
You will need Ocaml, ocamlfind, ocamlbuild, and OUnit2.

To build the project, clone the repo and then run `make build` in your local copy.
This should produce a file called `main.native`.

When you have a program you want to run, say `my_program.evco`, just run `./main.native my_program.evco`.
This will result in an error message if your program is not well-typed, otherwise it will print the type of your program (the type of its final value, usually `unit`), followed by any output from the program.

You can also run my unit tests by running `make test` which will build the test file and run it, use `make clean` to delete the `main.native` and `tests.native` executables from your directory, or use `make doc` do generate documentation for the source code (which may inadvertantly create the `main.native` file when rebuilding the code).

I have only tested this on ubuntu so you may run into trouble with the makefile and newlines if you try running this on a non-unix system.

## Example Code

Lists are defined by the code

```
newtype list 'a = Nil unit | Cons ('a * (list 'a)) in
```
which is included in all files before typechecking, and so is the function `map` which is defined by

```
{-- return lst with f applied to every entry --}
let rec map f lst =  
  match lst with    
  | Nil x -> Nil    
  | Cons pair ->   
  Cons(f (proj 2 0 pair), map f (proj 2 1 pair))
```

In this code snippet I print out the squares of the integers 0 through 10.

```evcolang
let ints_up_to n =
  if n < 0 then Nil else
  let rec helper k =
    if k > n then Nil else
    Cons(k,helper (k+1))
  in
  helper 0
in

let square x = x * x in

map print (map square (ints_up_to 10))

```

Asking for the type of `map print` will give back `∀ printable α. list α →  list unit` which says that it is a function that takes in a list of printable elements and returns a list of units.
This example is included in the repo as `print_squares.evco`.

The option type is also automatically included in every file and has the definition
```
newtype option 'a = None unit | Some 'a in
```

Here is another code snippet that computes the chinese remainder theorem map. It also shows how integer division and the modulo operators have been added and return `option` types (there are no exceptions in the language).


```
{-- this will compute the chinese remainder theorem map --}

let rec gcd_w_proof n m =
  if m = 0 then
  {-- guarantee that we give positive gcd --}
  if n > 0 then (n,1,0)
  else ((-n),(-1),0)
  else
  let x = n / m in
  match x with
  {-- None never happens --}
  Some x ->
    let q = proj 2 0 x in
    let r = proj 2 1 x in
    let rec_result = gcd_w_proof m r in
    let g = proj 3 0 rec_result in
    let s = proj 3 1 rec_result in
    let t = proj 3 2 rec_result in
    (g,t,s + (-(t*q)))
in

{-- compute basis for map Z_m * Z_n -> Z_mn --}
let basis n m =
  if (m = 0) or (n = 0) then None else
  let gcd_res = gcd_w_proof n m in
  if (proj 3 0 gcd_res) = 1 then
  Some (
    match (1 + ((-(proj 3 2 gcd_res))*m)) % (m * n) with
    Some y ->
      match (1 + ((-(proj 3 1 gcd_res))*n)) % (m * n) with
      Some x ->
        (x,y)
  )
  else None
in

{-- chinese_remainder n p m q is:
  if p and q are relatively prime: Some k where k is the unique integer between 0 and |pq| - 1 that is equivalent to n mod p and m mod q
  otherwise: None --}
let chinese_remainder n p m q =
  let pqbasis = basis p q in
  match pqbasis with
  | None x -> None
  | Some x ->
  (((proj 2 0 x) * n) + ((proj 2 1 x) * m)) % (p * q)
in

match chinese_remainder 2 23 1 5 with
Some x -> print x
{-- 71 --}
```

This example is included in the repo as `chinese_remainder.evco`.

Despite there being no exceptions, you can see that it is still possible to not match every case in match expressions.
In the case that you give it an input that is not matched, the evaluator will crash with a message saying that a case was unmatched, but the message is fairly cryptic so make sure you never write programs where this could happen.
This is necessary if you ever want to escape the `option` type.
For instance, in `gcd_w_proof` we would have to have it return an `option` type if we matched the `None` case, but we already checked if `m = 0` so that we know no crash will occur, and skipping this case allows us to return a bare `int` type instead of something of type `option int`.
I am considering modifying this so that you can have it crash with a custom message, but do not intend to add exceptions to the language, i.e. you will not be able to catch an exception, but just change the message that comes out.

## Important Notes

Although an expression like `proj 2 0 x` may look like a function---`proj`---applied to three arguments, `proj` is built-in syntax whose first two arguments must be integer literals that does not support partial application. So an expression like `proj (2+3) 2 x` is not valid, and neither is `let f = proj 2 0 in f x`.

Similarly, none of the binary infix operations allow partial application, so that `let f = (3+) in ...` is not valid either.

## Known Issues

The language is a toy language so I have not added a lot of obvious features that any real language needs (like support for strings) which is no surprise.
However, I would still like to create useful errror messages when a program fails to typecheck and allow the user to create custom error messages if there is an unmatched case at runtime, so I may add these fixes in the future.


