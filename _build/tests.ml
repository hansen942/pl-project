open OUnit2 open Definitions
open List
open Typecheck

let init_name = Sub 0
(* use only with strings that parse, will throw error otherwise, gives back typed_sugar and fresh_name *)
let tsug_from_string s =
  let lexbuf = Lexing.from_string s in
  let opt_t_e = Parser.prog Lexer.token lexbuf in
  annotate_opt_t_expr opt_t_e init_name 

(** [run_prog] first typechecks its input, then evaluates it. init_name is a name that is not currently used as a type variable*)
let run_prog tsugar init_name =
  let t,e,n = typecheck tsugar init_name in
  Evallambda.eval (desugar e)

let quick_get_type tsugar = match (typecheck tsugar init_name) with x,_,_ -> x
let quick_get_type_w_start tsugar init_name = match (typecheck tsugar init_name) with x,_,_ -> x
let quick_show_type tsugar = print_endline (string_of_class_constrained_expr_type (quick_get_type tsugar))
let simple_type tsugar = fst (quick_get_type tsugar) 
let simple_type_w_start e start = match (typecheck e start) with x,_,_ -> fst x
let show_type_w_start tsugar start = print_endline (string_of_class_constrained_expr_type (match (typecheck tsugar start) with x,_,_ -> x))

let int_id = fst(tsug_from_string "lambda x : int . x") 
let just_int = fst(tsug_from_string "0") 
let just_bool = fst(tsug_from_string "false")
let just_unit = fst(tsug_from_string "()")
let int_sum = fst(tsug_from_string "2 + 3")
let if_else = fst(tsug_from_string "if true then 0 else 1")

let simple_tests = "test suite without lets or polymorphism" >::: [
  "int_id" >:: (fun _ -> assert_equal (Fun(Integer,Integer)) (simple_type int_id));
  "int_sum" >:: (fun _ -> assert_equal Integer (simple_type int_sum));
  "just_int" >:: (fun _ -> assert_equal Integer (simple_type just_int));
  "just_bool" >:: (fun _ -> assert_equal Boolean (simple_type just_bool));
  "if_else" >:: (fun _ -> assert_equal Integer (simple_type if_else));
]

let id =  (TLambda (TVar (Name "x"),Name "x",TypeVar (Name "a")))
let print =  (TLambda (TPrint(TVar (Name "x")),Name "x",TypeVar (Name "a")))
let print_f_x =  (TLambda (TLambda(TPrint(TApplication(TVar (Name "f"), TVar (Name "x"))),Name "x",TypeVar (Name "b")),Name "f",TypeVar (Name "a")))

(* tests that types are right, ignores type classes though *)
let poly_tests = "test suite with polymorphism" >::: [
  "int_id" >:: (fun _ -> assert_equal true (match simple_type id with Fun(TypeVar a, TypeVar b) -> a = b | _ -> false));
  "print" >:: (fun _ -> assert_equal true (match simple_type print with Fun(TypeVar a,UnitType) -> true | _ -> false));
  "print_f_x" >:: (fun _ -> assert_equal true (match simple_type print_f_x with Fun(Fun(TypeVar a, TypeVar b),Fun(TypeVar c, UnitType)) -> a = c | _ -> false));
]


let fstlet = TLet (Name "x", TypeVar(Name "a") , (TInt 5), (TVar (Name "x")))
let nested_let = TLet(Name "x", TypeVar(Name "a"), (TInt 1), TLet (Name "x", TypeVar(Name "b"), (TBool true), (TVar (Name "x"))))
(* this expression is interesting because this requires inference to instantiate type variables distinctly for each isntance *)
let interesting = TLet(Name "x", TypeVar(Name "c"), id, (TApplication(TVar(Name "x"), TVar(Name "x"))))

let let_tests = "test suite with let expressions" >::: [
  "fstlet" >:: (fun _ -> assert_equal Integer (simple_type fstlet));
  "nested_let" >:: (fun _ -> assert_equal Boolean (simple_type nested_let));
  "id_itself" >:: (fun _ -> assert_equal true (match simple_type interesting with
                  | (Fun(TypeVar a, TypeVar b)) -> a = b
		  | _ -> false));
   
]

let fact,fact_start = tsug_from_string "let rec fact = lambda x . if x = 0 then 1 else x * (fact (x + (-1))) in fact"
(* I was concerned that f would not get assigned forall a. a -> a but rather get forall a. a *)
let subtle,subtle_start = tsug_from_string "let rec f = lambda x . x in f"
let fib,fib_start = tsug_from_string 
"let fib n =
  let rec fib_help a b n =
    if n = 0 then a else
    if n = 1 then b else
    fib_help b (a+b) (n+(-1))
  in fib_help 0 1 n
in
fib"

let let_rec_tests = "test suite with let rec expressions" >::: [
  "fact" >:: (fun _ -> assert_equal (Fun(Integer,Integer)) (simple_type_w_start fact fact_start));
  "subtle" >:: (fun _ -> assert_equal true (match (simple_type_w_start subtle subtle_start) with Fun(TypeVar a, TypeVar b) -> a = b | _ -> false));
  "fib" >:: (fun _ -> assert_equal (Fun(Integer,Integer)) (simple_type_w_start fib fib_start));
]

let infer_prod,infer_prod_start = tsug_from_string "lambda x . print (proj 2 0 x)"
(* this test shows our inference constrains to the specified type *)
let annotated,annotated_start = tsug_from_string "let rec f : int -> int = lambda x . x in f"

let infer_tests = "test suite for type inference" >::: [
  "annotated" >:: (fun _ -> assert_equal (Fun(Integer,Integer)) (simple_type_w_start annotated annotated_start));
  "product_fun" >:: (fun _ -> assert_equal true (match (simple_type_w_start infer_prod infer_prod_start) with
      | Fun(Product [TypeVar a; TypeVar b], UnitType) -> a <> b
      | _ -> false));
]
let simple_sum,simple_sum_start = tsug_from_string 
"match Some 103 with
| Some x -> x
| None x -> 0"
let first_list,first_list_start = tsug_from_string
"let first_list = Cons (1, Cons(2, Nil)) in
first_list"

let sum_tests = "test suite for sum types" >::: [
  "simple_sum" >:: (fun _ -> assert_equal Integer (simple_type_w_start simple_sum simple_sum_start));
  "first_list" >:: (fun _ -> assert_equal (SumType("list",[Integer])) (simple_type_w_start first_list first_list_start));
]

let class_permanence,class_permanence_start = tsug_from_string 
"let f x : 'c -> unit = let a : 'a = print(proj 2 0 x) in print(proj 2 1 x) in f"

let class_test _ =
  match quick_get_type_w_start class_permanence class_permanence_start with
  | (t,class_constraints) ->
      match t with
      | Fun(Product [TypeVar a;TypeVar b], UnitType) -> (
        match assoc_opt a class_constraints, assoc_opt b class_constraints with
        | Some [Printable], Some [Printable] -> true
        | _, _ -> false
        
      )
      | _ -> false


let tclass_tests = "test suite that makes sure that some tricky type class inferences work" >::: [
  "lets don't lose classes" >:: (fun _ -> assert_equal true (class_test ()))
]

let type_test_suite = "type tests" >::: [simple_tests;poly_tests;let_tests;let_rec_tests;infer_tests;sum_tests;tclass_tests]

let fact_5,fact_5_start = tsug_from_string "let rec fact x = if x = 0 then 1 else x * (fact (x + (-1))) in fact 5"
let app_prod = ( (TApplication( infer_prod, TProd[TInt 5; TBool false])))

let run_prog_tests = "test suite that uses main to run some test programs" >:::[
  "fact_5" >:: (fun _ -> assert_equal (Int 120) (run_prog fact_5 fact_5_start));
  "app_prod" >:: (fun _ -> assert_equal Unit (run_prog app_prod infer_prod_start));
]


let end_to_end_tests = "end-to-end tests" >::: [run_prog_tests]

let test_suite = "test suite" >::: [type_test_suite; end_to_end_tests]
let _ = run_test_tt_main test_suite

