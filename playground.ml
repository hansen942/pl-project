open Definitions
open Typecheck
(* test that Evallambda.eval gives back values*)

(*let test_on e =
Printf.printf "Evallambda.evaluation of %s:" (string_of_sugar e);
print_newline ();
print_string (string_of_expr (Evallambda.eval (desugar e)));
print_newline ()
*)
(*
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
*)

(*
let show_type texpr =
  match typecheck texpr with
  | Left msg -> print_endline msg
  | Right t -> print_endline (string_of_type (fst t))

let tfact =
  let n = Name "n" in
  let fact = Name "tfact" in
  TBase (TLambda (TIf(TEq(TVar n,TInt 0),TInt 1, TTimes(TVar n,TApplication (TVar fact, TPlus (TVar n,TInt (-1))))), n, Integer))
let tfact5 = TLetRec (Name "tfact", Fun(Integer,Integer), tfact, TBase(TApplication (TVar (Name "tfact"),TInt 3))) 

let full_eval texpr =
  Printf.printf "starting on\n%s" (string_of_typed_sugar texpr); print_newline ();
    print_endline "type checking...";
    match typecheck texpr with
    | Left msg -> Printf.printf "type checking failed with error %s" msg
    | Right (t,e) ->
      Printf.printf "type of expression is %s" (string_of_type t);
      print_newline ();
      print_endline "evaluating expression...";
      let result = Evallambda.eval (desugar e) in
      print_endline (string_of_expr result)

let _ = full_eval tfact5

let nested_let = TLet(Name "x", TBase (TInt 1), TLet (Name "x", TBase(TBool true), TBase(TVar (Name "x"))))
let _ = full_eval nested_let

let test_print = TLet(Name "x", TBase (TInt 1), TBase (TPrint (TVar (Name "x"))))
let _ = full_eval test_print
*)

let tsug_from_string s =
  let lexbuf = Lexing.from_string s in
  let opt_t_e = Parser.prog Lexer.token lexbuf in
  annotate_opt_t_expr opt_t_e init_name 

let fact,fact_start = tsug_from_string "let rec fact = lambda x . if x = 0 then 1 else x * (fact (x + (-1))) in fact"

let _ = print_endline (string_of_class_constrained_expr_type (fst (typecheck fact fact_start)))
