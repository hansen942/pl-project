# A Small Functional Language
The goal of the project is to build a small ml-like functional language that is strongly typed and supports type inference, polymorphism, recursion, etc.
Some other cool features I am thinking of adding include Haskell-style functors and monad syntax (maybe do notation).
## Status
The language is based off the applied lambda calculus extended with let statements.
It also supports user defined algebraic data types, prenex polymorphism type inference, and I am working to add type classes.

Currently the only type class is the type class `printable` of types that can be printed with the built-in print function, but type class inference has soundness issues (this does not lead to crashes, but it will sometimes allow you to print things like functions that typically will not be very readable).
I am working on removing this bug.
It is currently not possible for the user to define typeclasses, but if/when I resolve this bug I will add this functionality as well.

## Example Code

Lists are defined by the code

```
newtype list 'a = Nil unit | Cons ('a * (list 'a)) in
```
which is included in all files before typechecking.

In this code snippet I write the `map` function for lists, then use this to print out the squares of the integers 0 through 10.

```evcolang
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
let rec print_list lst = map print lst
in

{-- print the squares of the integers 0 through 10 --}
print_list (map (lambda x . x * x) (ints_up_to 10))
```

The soundness issue with type classes can be demonstrated here by asking the typechecker what the type of `print_list` is; it will tell you it has the type `forall 'a. list 'a -> list unit` when it should say `forall printable 'a. list 'a -> list unit`. I.e. it will allow you to print lists of items even if these items are not in the `printable` typeclass.


The option type is also automatically included in every file and has the definition
```
newtype option 'a = None unit | Some 'a in
```

Here is another code snippet that computes the chinese remainder theorem map. It also shows how integer division and the modulo operators have been added and return option types (there are no exceptions in the language).


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

{-- If p is relatively prime to q then this returns Some k where k is the unique integer between 0 and pq - 1 that is equivalent to n mod p and m mod q--}
let chinese_remainder n p m q =
  let pqbasis = basis p q in
  match pqbasis with
  | None -> lambda x . None
  | Some -> lambda x .
  (((proj 2 0 x) * n) + ((proj 2 1 x) * m)) % (p * q)
in

match chinese_remainder 2 23 1 5 with
Some -> lambda x . print x
{-- prints 71 --}
```

Despite there being no exceptions, you can see that it is still possible to not match every case in match expressions.
In the case that you give it an input that is not matched, the evaluator will crash.
This is necessary if you ever want to get outside the `option` type.
For instance, in `gcd_w_proof` we would have to have it return an `option` type if we matched the `None` case, but we already checked if `m = 0` so that we know no crash will occur.
I am considering modifying this so that you can have it crash with a custom message, but do not intend to add exceptions to the language, i.e. you will not be able to catch an exception, but just change the message that comes out.
