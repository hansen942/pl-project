open OUnit2
open Definitions
open Typecheck
open Main

let show_type tsugar = print_endline (string_of_class_constrained_expr_type (fst (typecheck tsugar)))
let simple_type e = fst(fst(typecheck e))

let int_id = TBase (TLambda (TVar (Name "x"),Name "x",Integer))
let just_int = TBase (TInt 0)
let just_bool = TBase (TBool true)
let just_unit = TBase TUnit
let int_sum = TBase (TPlus(TInt 2, TInt 3))
let if_else = TBase(TIf(TBool true, TInt 0, TInt 1))

let simple_tests = "test suite without lets or polymorphism" >::: [
  "int_id" >:: (fun _ -> assert_equal (Fun(Integer,Integer)) (simple_type int_id));
  "int_sum" >:: (fun _ -> assert_equal Integer (simple_type int_sum));
  "just_int" >:: (fun _ -> assert_equal Integer (simple_type just_int));
  "just_bool" >:: (fun _ -> assert_equal Boolean (simple_type just_bool));
  "if_else" >:: (fun _ -> assert_equal Integer (simple_type if_else));
]

let id = TBase (TLambda (TVar (Name "x"),Name "x",TypeVar (Name "a")))
let print = TBase (TLambda (TPrint(TVar (Name "x")),Name "x",TypeVar (Name "a")))
let print_f_x = TBase (TLambda (TLambda(TPrint(TApplication(TVar (Name "f"), TVar (Name "x"))),Name "x",TypeVar (Name "b")),Name "f",TypeVar (Name "a")))

(* tests that types are right, ignores type classes though *)
let poly_tests = "test suite with polymorphism" >::: [
  "int_id" >:: (fun _ -> assert_equal true (match simple_type id with Fun(TypeVar a, TypeVar b) -> a = b | _ -> false));
  "print" >:: (fun _ -> assert_equal true (match simple_type print with Fun(TypeVar a,UnitType) -> true | _ -> false));
  "print_f_x" >:: (fun _ -> assert_equal true (match simple_type print_f_x with Fun(Fun(TypeVar a, TypeVar b),Fun(TypeVar c, UnitType)) -> a = c | _ -> false));
]


let fstlet = TLet (Name "x", TBase(TInt 5), TBase(TVar (Name "x")))
let nested_let = TLet(Name "x", TBase (TInt 1), TLet (Name "x", TBase(TBool true), TBase(TVar (Name "x"))))
(* this expression is interesting because this requires inference to instantiate type variables distinctly for each isntance *)
let interesting = TLet(Name "x", id, TBase(TApplication(TVar(Name "x"), TVar(Name "x"))))

let let_tests = "test suite with let expressions" >::: [
  "fstlet" >:: (fun _ -> assert_equal Integer (simple_type fstlet));
  "nested_let" >:: (fun _ -> assert_equal Boolean (simple_type nested_let));
  "id_itself" >:: (fun _ -> assert_equal true (match simple_type interesting with
                  | (Fun(TypeVar a, TypeVar b)) -> a = b
		  | _ -> false));
   
]

let fact' =
  let n = Name "n" in
  TBase (TLambda (TIf(TEq(TVar n,TInt 0),TInt 1, TTimes(TVar n,TApplication (TVar (Name "f"), TPlus (TVar n,TInt (-1))))), n, TypeVar (Name "a")))
let fact = TLetRec(Name "f", TypeVar (Name "b") , fact', TBase(TVar (Name "f")))

let let_rec_tests = "test suite with let rec expressions" >::: [
  "fact" >:: (fun _ -> assert_equal (Fun(Integer,Integer)) (simple_type fact));
]

let infer_prod = TBase (TLambda (TPrint(TProj (TVar (Name "x"),0,2)), Name "x", TypeVar (Name "a")))

let infer_tests = "test suite for type inference" >::: [
  "product_fun" >:: (fun _ -> assert_equal true (match simple_type infer_prod with
      | Fun(Product [TypeVar a; TypeVar b], UnitType) -> a <> b
      | _ -> false));
]

let type_test_suite = "type tests" >::: [simple_tests;poly_tests;let_tests;let_rec_tests;infer_tests]

let fact_5 = (TLetRec(Name "f",TypeVar (Name "c"),fact',TBase(TApplication(TVar(Name "f"), TInt 5))))
let app_prod = (TBase (TApplication(quick_strip_tsugar infer_prod, TProd[TInt 5; TBool false])))

(* fails because substitution not implemented for products yet *)
let run_prog_tests = "test suite that uses main to run some test programs" >:::[
  "fact_5" >:: (fun _ -> assert_equal (Int 120) (run_prog fact_5));
  "app_prod" >:: (fun _ -> assert_equal Unit (run_prog app_prod));
]

let end_to_end_tests = "end-to-end tests" >::: [run_prog_tests]

let test_suite = "test suite" >::: [type_test_suite; end_to_end_tests]
let _ = run_test_tt_main test_suite
