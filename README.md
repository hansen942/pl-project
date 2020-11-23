# A Small Functional Language
The goal of the project is to build a small ml-like functional language that is strongly typed and supports type inference, polymorphism, recursion, etc.
Some other cool features I am thinking of adding include Haskell-style functors and monad syntax (maybe do notation).
## Status
I began by implementing an evaluator for the applied lambda calculus with integers and booleans.
Then I made it simply typed and added recursive functions.
Then I implemented prenex polymorphism type inference and type classes (currently the only type class is the `printable` class of types that can be printed).
Next, I built the lexer and parser.
Recently I added product types and (recursive) sum types.

## Example Code
In this code snippet I define the type of lists, write the `map` function for lists, then use this to print out the squares of the integers 0 through 10.

```evcolang
newtype list 'a = Nil unit | Cons ('a * (list 'a)) in

{-- map f lst gives back the list that is the result of applying f to each element of lst --}
let rec map f lst =
  match lst with
  | Nil -> lambda x . Nil
  | Cons -> lambda pair .
    Cons(f (proj 2 0 pair), map f (proj 2 1 pair))
in

{-- ints_up_to n is the list of integers 0 up to n; fails if n < 0 --}
let ints_up_to n =
  let rec helper k n =
    if k = n + 1 then Nil
    else Cons(k,helper (k+1) n)
  in
  helper 0 n
in

{-- prints every element in the list lst --}
let rec print_list lst =
  match lst with
  | Nil -> lambda x . ()
  | Cons -> lambda x .
    let a = print (proj 2 0 x) in
    print_list (proj 2 1 x)
in

{-- print the squares of the integers 0 through 10 --}
print_list (map (lambda x . x * x) (ints_up_to 10))
```

Here is another code snippet that computes the chinese remainder theorem map. It also shows how integer division and the modulo remainders have been added and return option types (there are no exceptions in the language).

```
{-- this will compute the chinese remainder theorem map --}

let rec gcd_w_proof n m =
  if m = 0 then
  {-- guarantee that we give positive gcd --}
  if n > 0 then (n,1,0)
  else ((-n),(-1),0)
  else
  let x = n / m in
  match x with Some ->
    lambda x .
    let q = proj 2 0 x in
    let r = proj 2 1 x in
    let rec_result = gcd_w_proof m r in
    let g = proj 3 0 rec_result in
    let s = proj 3 1 rec_result in
    let t = proj 3 2 rec_result in
    (g,t,s + (-(t*q)))
in

{-- compute basis for map Z_mn -> Z_m * Z_n--}
let basis n m =
  if (m = 0) or (n = 0) then None () else
  let gcd_res = gcd_w_proof n m in
  if (proj 3 0 gcd_res) = 1 then
  Some (
    match (1 + ((-(proj 3 2 gcd_res))*m)) % (m * n) with
    Some -> lambda y : int .
      match (1 + ((-(proj 3 1 gcd_res))*n)) % (m * n) with
      Some -> lambda x : int .
        (x,y)
  )
  else None ()
in

let chinese_remainder n p m q =
  let pqbasis = basis p q in
  match pqbasis with
  | None -> lambda x . None
  | Some -> lambda x .
  (((proj 2 0 x) * n) + ((proj 2 1 x) * m)) % (p * q)
in

match chinese_remainder 2 23 1 5 with
Some -> lambda x . print x
```
