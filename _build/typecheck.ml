open Definitions
(** the [either] monad allows us to express failure in a principled way*)
type ('a,'b) either = Left of 'a | Right of 'b
let return a = Right a
let (>>=) e f =
match e with
| Left a -> Left a
| Right a -> f a

(** [let*] gives us some noice syntax similar to [do] notation in Haskell*)
let (let*) x f = x >>= f

(** [info] should be line and column info *)
type info = int * int

(* [error_msg] tells what went wrong during type checking *)
type error_msg = string

let strip (tsugar:typed_sugar) : sugar = failwith "strip unimplemented"

let desugar (tsugar:typed_sugar) : typed_expr = failwith "desugar unimplemented"

(** [tcheck t_expr] *)
let tcheck : typed_expr -> (error_msg,expr_type) either = function
| _ -> Right Unit

let typecheck sugar_e =
  let no_sugar = desugar sugar_e in
  let* mtype = tcheck no_sugar in
  return (mtype, strip sugar_e)

