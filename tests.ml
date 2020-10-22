 open Evallambda
open Definitions
(* test that eval gives back values*)

let test_on e =
Printf.printf "evaluation of %s:" (string_of_expr e);
print_newline ();
print_string (string_of_expr (eval e));
print_newline ()

let _ = test_on (Int 5)

let _ = test_on (Lambda (Var (Name "x"), Name "x"))

let _ = test_on (Application (Lambda (Var (Name "x"), Name "x"), Lambda (Var (Name "x"), Name "x")))

let _ = test_on (Application (Lambda (Application(Var (Name "x"), Var (Name "x")), Name "x"), Lambda (Var (Name "x"), Name "x")))

let _ = test_on (If (Bool true, Int 1, Int 0))

let fact' =
  let n = Name "n" in
  Lambda (Lambda (If(Eq(Var n,Int 0),Int 1, Times(Var n,Application (Var (Name "f"), Plus (Var n,Int (-1))))), n), Name "f")
let fact = Application(Z,fact')

let _ = test_on (Application(fact,Int 5))
