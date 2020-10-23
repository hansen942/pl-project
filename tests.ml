open Evallambda
open Definitions
open Typecheck
(* test that eval gives back values*)

let test_on e =
Printf.printf "evaluation of %s:" (string_of_sugar e);
print_newline ();
print_string (string_of_expr (eval (desugar e)));
print_newline ()

(*
let _ = test_on (Base (Int 5))

let _ = test_on (Base (Lambda (Var (Name "x"), Name "x")))

let _ = test_on (Base (Application (Lambda (Var (Name "x"), Name "x"), Lambda (Var (Name "x"), Name "x"))))

let _ = test_on (Base (Application (Lambda (Application(Var (Name "x"), Var (Name "x")), Name "x"), Lambda (Var (Name "x"), Name "x"))))

let _ = test_on (Base (If (Bool true, Int 1, Int 0)))
*)
(* fact is the factorial function, assuming that "f" is the name it is assigned to *)
let fact =
  let n = Name "n" in
  Base (Lambda (If(Eq(Var n,Int 0),Int 1, Times(Var n,Application (Var (Name "f"), Plus (Var n,Int (-1))))), n))
(* this is let rec f = <<fact>> in f 5*)
let fact5 = 
  LetRec(Name "f", fact, Base(Application (Var (Name "f"), Int 5)))

let _ = test_on fact5
(*
(* this is the expression let x = 0 in let rec x = x + 1 in x which does not terminate because x = x + 1 has no fixed point *)
let bad_rec = Let(Name "x", Base(Int 0), LetRec (Name "x", Base (Plus (Var (Name "x"), Int 1)), Base(Var (Name "x"))))

let _ = print_endline (string_of_sugar bad_rec)

(* This also does not terminate because although it has a fixed point, the recursion will never find it.*)
let weird_rec =
  let x = Name "x" in
  Let(x,Base(Int 1),LetRec(x,Base(If(Eq(Var x,Int 0),Var x,Plus(Var x, Int (-1)))),Base (Var x)))

(* This is the same expression as weird_rec but using let not let rec. It terminates. *)
*)let weird_non_rec =
  let x = Name "x" in
  Let(x,Base(Int 1),Let(x, Base(Plus(Var x, Int 1)),Base (Var x)))

let _ = test_on weird_non_rec

