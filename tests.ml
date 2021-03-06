open OUnit2 open Definitions
open Typecheck

let init_name = Sub 0
(* use only with strings that parse, will throw error otherwise, gives back typed_sugar and fresh_name *)
let tsug_from_string s =
  let lexbuf = Lexing.from_string s in
  let from_parser_t_e = Parser.prog Lexer.token lexbuf in
  let fresh = ref init_name in
  info_of_from_parser fresh from_parser_t_e, fresh

(** [run_prog] first typechecks its input, then evaluates it. init_name is a name that is not currently used as a type variable*)
let run_prog info init_name =
  let t,e,n = typecheck info (ref init_name) in
  Evallambda.eval (desugar e) init_name

let quick_get_type tsugar = match (typecheck tsugar (ref (Sub 10))) with x,_,_ -> x
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

let id = fst (tsug_from_string "lambda x . x")
let print = fst (tsug_from_string "lambda x . print x")
let print_f_x = fst (tsug_from_string "lambda f . lambda x . print (f x)") 

(* tests that types are right, ignores type classes though *)
let poly_tests = "test suite with polymorphism" >::: [
  "int_id" >:: (fun _ -> assert_equal true (match simple_type id with Fun(TypeVar a, TypeVar b) -> a = b | _ -> false));
  "print" >:: (fun _ -> assert_equal true (match simple_type print with Fun(TypeVar a,UnitType) -> true | _ -> false));
  "print_f_x" >:: (fun _ -> assert_equal true (match simple_type print_f_x with Fun(Fun(TypeVar a, TypeVar b),Fun(TypeVar c, UnitType)) -> a = c | _ -> false));
]


let fstlet = fst (tsug_from_string "let x = 5 in x")
let nested_let = fst (tsug_from_string "let x = 1 in let x = true in x")
(* this expression is interesting because this requires inference to instantiate type variables distinctly for each isntance *)
let interesting = fst (tsug_from_string "let x = lambda x . x in x x")

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

let type_test_suite = "type tests" >::: [simple_tests;poly_tests;let_tests;let_rec_tests;infer_tests;sum_tests]

let fact_5,fact_5_start = tsug_from_string "let rec fact x = if x = 0 then 1 else x * (fact (x + (-1))) in fact 5"
let app_prod = ( (IApplication(infer_prod, IProd([IInt (5,Lexing.dummy_pos); IBool(false,Lexing.dummy_pos)],Lexing.dummy_pos), Lexing.dummy_pos)))

let run_prog_tests = "test suite that uses main to run some test programs" >:::[
  "fact_5" >:: (fun _ -> assert_equal (Int 120) (run_prog fact_5 !fact_5_start));
  "app_prod" >:: (fun _ -> assert_equal Unit (run_prog app_prod !infer_prod_start));
]


let end_to_end_tests = "end-to-end tests" >::: [run_prog_tests]

let test_suite = "test suite" >::: [type_test_suite; end_to_end_tests]
let _ = run_test_tt_main test_suite 

