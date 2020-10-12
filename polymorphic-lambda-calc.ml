open Printf
open Printexc
exception TypeError
exception StuckExpression
exception UnboundVariable
exception ExpectedSomething

type var = int
type tvar = int

let force_extract a =
match a with
| Some x -> x
| _ -> raise ExpectedSomething

(* Note: user code should only use tvar >= 0, the negative values are reserved for use in desugaring*)
type t =
| Integer
| Fun of t * t
| TVar of tvar * bool (* the bool is true iff this comes from user *)
| Boolean

type type_annotation = t option

let rec showt t =
match t with
| Integer -> "int"
| Boolean -> "bool"
| TVar (x,u) -> "t" ^ (string_of_int x)
| Fun (t1,t2) -> (showt t1) ^ " → " ^ (showt t2)

(* For some reason ocaml is not using my error printouts I set up here. Figure out why. *)
exception FalsePolymorphism of tvar * t
let () =
  Printexc.register_printer
    (function
      | FalsePolymorphism (varnum, expected) -> Some (Printf.sprintf "User annotated type variable t(%d) but inferred constraint t(%d) = (%s). Please replace the type variable with the concrete type or remove the annotation to have it filled automatically." varnum varnum (showt expected))
      | _ -> None (* for other exceptions *)
    )

type expr_annotated =
| Int of int
| Var of var
| Lambda of expr_annotated * type_annotation (*type annotation is arg type*)
| Application of expr_annotated * expr_annotated
| If of expr_annotated * expr_annotated * expr_annotated
| Bool of bool
| Plus of expr_annotated * expr_annotated
| Times of expr_annotated * expr_annotated

type expr =
| Int of int
| Var of var
| Lambda of expr * t (*type annotation is arg type*)
| Application of expr * expr
| If of expr * expr * expr
| Bool of bool
| Plus of expr * expr
| Times of expr * expr

let rec fill_in_annotations (ea : expr_annotated) (curr_name : int) : expr =
match ea with
| Lambda (e, Some t) -> Lambda (fill_in_annotations e curr_name, t)
| Lambda (e, None) -> Lambda (fill_in_annotations e (curr_name - 1), TVar (curr_name, false))
| Application (e1,e2) -> Application (fill_in_annotations e1 curr_name, fill_in_annotations e2 curr_name)
| If (e1,e2,e3) -> If (fill_in_annotations e1 curr_name, fill_in_annotations e2 curr_name, fill_in_annotations e3 curr_name)
| Plus (e1,e2) -> Plus (fill_in_annotations e1 curr_name, fill_in_annotations e2 curr_name)
| Times (e1,e2) -> Times (fill_in_annotations e1 curr_name, fill_in_annotations e2 curr_name)
| Int n -> Int n
| Var v -> Var v
| Bool b -> Bool b


type sugary_expr = 
| Base of expr_annotated
| Let of sugary_expr * sugary_expr 

let rec desugar_help sugary depth =
match sugary with
| Base expr -> fill_in_annotations expr depth
| Let (s1,s2) -> Application (Lambda (desugar_help s2 (depth - 1), TVar (depth, false)), desugar_help s1 depth)

let desugar sugary = desugar_help sugary (-1)

let rec shift c i expr =
match expr with
| Int n -> Int n
| Bool b -> Bool b
| If (g,e1,e2) -> If (shift c i g, shift c i e1, shift c i e2)
| Plus (e1,e2) -> Plus (shift c i e1, shift c i e2)
| Times (e1,e2) -> Times (shift c i e1, shift c i e2)
| Var n -> if n < c then Var n else Var (n + i)
| Lambda (e,t) -> Lambda (shift (c+1) i e, t)
| Application (l1, l2) -> let s = shift c i in Application (s l1, s l2)

let rec showe expr =
match expr with
| Int n -> string_of_int n
| Var v -> "v" ^ (string_of_int v)
| Lambda (e,t) -> "λ.(" ^ (showe e) ^ ")"
| Application (l1, l2) -> "(" ^ (showe l1) ^ " " ^ (showe l2) ^ ")"
| If (g,e1,e2) -> "if " ^ (showe g) ^ " then " ^ (showe e1) ^ " else " ^ (showe e2)
| Bool b -> if b then "true" else "false"
| Plus (x,y) -> (showe x) ^ " + " ^ (showe y)
| Times (x,y) -> (showe x) ^ " * " ^ (showe y)


let rec sub e1 e2 m =
match e1 with
| Bool b -> Bool b
| Int n -> Int n
| If (g,first,second) -> If (sub g e2 m, sub first e2 m, sub second e2 m)
| Plus (x,y) -> Plus (sub x e2 m, sub y e2 m)
| Times (x,y) -> Times (sub x e2 m, sub y e2 m)
| Var v -> if m = v then e2 else Var v
| Lambda (e,t) -> Lambda (sub e (shift 0 1 e2) (m+1), t)
| Application (l1, l2) -> Application ((sub l1 e2 m),(sub l2 e2 m))


(* This is the small step semantics *)
let rec smallstep (expr:expr) : expr=
  match expr with
  | Plus (x,y) -> handle_plus x y
  | Times (x,y) -> handle_times x y
  | Int n -> Int n
  | Var v -> Var v
  | Bool b -> Bool b
  | If (g,first,second) -> handle_if g first second
  | Lambda (e,t) -> Lambda (e,t)
  | Application (e1, e2) -> (* We use CBV *)
    match e1 with
    | Lambda (e,t) ->
      (
      match e2 with
      | Int _ -> shift 0 (-1) (sub e (shift 0 1 e2) 0)
      | Lambda _ -> shift 0 (-1) (sub e (shift 0 1 e2) 0)
      | Application _ -> Application (e1, smallstep e2)
      | Var _ -> raise StuckExpression
      | Plus _ -> Application (e1, smallstep e2)
      | Times _ -> Application (e1, smallstep e2)
      | If _ -> Application (e1, smallstep e2)
      | Bool _ -> shift 0 (-1) (sub e (shift 0 1 e2) 0)
      )
    | Int _ -> raise TypeError
    | Bool _ -> raise TypeError
    | _ -> Application(smallstep e1, e2)

and handle_if g first second =
match g with
| Bool b -> if b then first else second
| _ -> If (smallstep g, first, second)

and handle_plus x y =
match x with
| Int xint ->
  (
  match y with
  | Int yint -> Int (xint + yint)
  | _ -> Plus (x, smallstep y)
  )
| _ -> Plus (smallstep x, y)

and handle_times x y =
match x with
| Int xint ->
  (
  match y with
  | Int yint -> Int (xint * yint)
  | _ -> Times (x, smallstep y)
  )
| _ -> Times (smallstep x, y)

(* Recursively substitute an inferred type for any type variables *)
let rec update_tvars t tenv =
match t with
| Integer -> Integer
| Boolean -> Boolean
| Fun (t,t') -> Fun (update_tvars t tenv, update_tvars t' tenv)
| TVar (n,u) ->
  match tenv n with
  | Some concrete -> concrete
  | None -> t 

type type_env = (int -> t option)
type update_flag = bool
(* NOTE: if update_flag is false then ignore any values in feedback *)
type feedback = type_env * type_env * type_env * update_flag (* venv, tenv, ogtenv *)
(* This is used to accumulate new type inferences and note whether any changes have been made. *)
let (>>) (updates : feedback) (f : type_env -> type_env -> type_env -> (type_env * type_env * type_env) option) : feedback =
  match updates with
  | (venv,tenv,ogtenv,flag) ->
  match f venv tenv ogtenv with
  | Some (new_venv, new_tenv, new_ogtenv) -> (new_venv, new_tenv, new_ogtenv, true)
  | None -> updates

let make_feed venv tenv ogtenv maybe_feed =
match maybe_feed with
| Some feed -> feed
| None -> (venv,tenv,ogtenv,false)

let update_tenv tenv n t = fun x -> if x = n then Some t else tenv x
let update_venv venv (tenv : type_env) = fun x ->
  match venv x with
  | None -> None
  | Some (TVar (n,u)) ->
    (match tenv n with
    | None -> Some (TVar (n,u))
    | Some t -> Some t)
  | _ -> venv x

let flag feedback =
match feedback with
| (_, (_, _, _, b)) -> b

(* Given tenv of type type_env we update the annotations of expr *)
let rec update_expr_annotations expr tenv =
let update expr = update_expr_annotations expr tenv in
match expr with
| Lambda (e,t) -> Lambda (e, update_tvars t tenv)
| Application (e1,e2) -> Application (update e1, update e2)
| If (g,e1,e2) -> If (update g,update e1,update e2)
| Plus (e1,e2) -> Plus (update e1, update e2)
| Times (e1,e2) -> Times (update e1, update e2)
| _ -> expr



(* Our type checker *)
(* venv is used to keep track of the known types of variables while tenv keeps track of hte known types of type variables
The point of also having ogtenv is that ogtenv is not updated when we infer a type from the left term of an application, and so can be
used to evaluate the type of the right term. It is necessary so that type-name-conflicts between a function
and its argument do not cause issues. This would arise from an application (t0 -> t1) (t0 -> t1) because we would substitute t0 = t0 -> t1 everywhere, resulting in a non-terminating type check.
The way this actually evaluates should be to the variable t1 (from the first function definition) *)
(* when you call tcheck on a subexpression you need to check if the flag is set in the feedback it returns, if it is then it has inferred some types so you have to infer them as well*)
(* If it does infer a type, then you update your tenv then call yourself on the exact expression you were called on but with the updated tenv, you then pass the feedback back up*)
(* Raises a TypeError if any type error occurs (currently with no info).
   Raises a FalsePolymorphism error if a user annotated type variable can be inferred (i.e. if it cannot actually be any type)*)
(* TODO: fix this so it doesn't overflow *)
let rec tcheck expr venv tenv ogtenv : t * feedback =
(*let _ = Printf.printf "Current evaluating the expression (%s)" (showe expr); print_newline () in*)
let no_feedback = (venv,tenv,ogtenv,false) in
match expr with
| Bool _ -> (Boolean, no_feedback)
| Int _ -> (Integer, no_feedback)
| If (guard,first,second) -> let t2 = check_type second in let feedback = make_feed venv tenv ogtenv None >> (verify_type guard Boolean) >> (verify_type first t2) in callback (t2,feedback) expr
| Plus (x,y) -> let feedback = make_feed venv tenv ogtenv None >> (verify_type x Integer) >> (verify_type y Integer) in callback (Integer,feedback) expr
| Times (x,y) -> let feedback = make_feed venv tenv ogtenv None >> (verify_type x Integer) >> (verify_type y Integer) in callback (Integer,feedback) expr
| Var v -> (match venv v with Some t -> (t, no_feedback) | _ -> raise UnboundVariable)
| Lambda (e,t) -> handle_lambda e t venv tenv ogtenv
| Application (e1, e2) ->
  match tcheck e1 venv tenv ogtenv with
  | (Fun(t, t'), (subvenv1,subtenv1,subogtenv1,flag1)) ->
    if flag1 then callback (t',(subvenv1, subtenv1, ogtenv, flag1)) expr else (* NOTE: weird to put t' in our feedback cuz don't know if that's right yet, but does not matter as will reevaluate *)
    (
    let (t2, (subvenv2, subtenv2, subogtenv2, flag2)) = tcheck e2 venv ogtenv ogtenv in
    if flag2 then callback (t2,(subvenv2, tenv, subogtenv2, flag2)) expr else (* concerned about which venv we are calling back with *)
    match t with
    | TVar (n,u) ->
      (match tenv n with
      | Some tknown -> if tknown = t2 then (update_tvars t' tenv, no_feedback)
	else raise TypeError
      | None -> let new_tenv x = if x = n then Some t2 else tenv x in tcheck (Application (e1,e2)) venv new_tenv tenv 
      )
    | _ -> if t2 = t then (t', no_feedback) else raise TypeError
    )
  | _ -> raise TypeError

(* helper to call type checker more easily *)
and check_type_verbose expr = tcheck expr (fun x -> None) (fun x -> None) (fun x -> None)
and check_type expr = fst (check_type_verbose expr)

(* used to automate letting calling oneself and sending feedback up*)
and callback output self =
match output with
| (t, (venv, tenv, ogtenv, flag)) ->
  if flag then
  ((*Printf.printf "Called back to expression (%s)" (showe self); print_newline ();
  Printf.printf "Found type was (%s)" (showt t); print_newline ();*)
  let updated_self = update_expr_annotations self tenv in
  match tcheck updated_self venv tenv ogtenv with
  | (t,(subvenv,subtenv,subogtenv,subflag)) -> (t,(update_venv subvenv subtenv,subtenv,subogtenv,true)))
  else (t, (venv, tenv, ogtenv, flag))

and handle_lambda e t venv tenv ogtenv =
  let new_venv x = if x = 0 then Some t else venv (x-1) in
  match tcheck e new_venv tenv ogtenv with
  | (te,(nvenv,ntenv,nogtenv,flag)) ->
    if flag then
    let nt = update_tvars t ntenv in
    (*as going outside the lambda have to shift the variables*)
    let outside_venv x = if not (x = (-1)) then venv (x+1) else None in
    (Fun (nt, te), (outside_venv,ntenv,nogtenv,flag)) 
    else (Fun (t,te), (venv,tenv,ogtenv,flag)) (* the data in this feedback is not valid so should not be used, its flag is false though so this should be fine *)

(* this function checks that echeck has type t in the given contexts;
if it does not then it checks if it is polymorphic, if so it updates the type environments and returns them, otherwise it throws a TypeError *)
and verify_type echeck t venv tenv ogtenv: (type_env * type_env * type_env) option =
  let (tfound, (subvenv, subtenv, subogtenv, flag)) = tcheck echeck venv tenv ogtenv in
  if tfound = t then (if not flag then None else Some (subvenv, subtenv, subogtenv))
  else
  match tfound with
  | TVar (n,u) ->
  if u then raise (FalsePolymorphism (n,t)) else
  let new_tenv = update_tenv subtenv n t in Some (update_venv venv new_tenv, update_tenv subtenv n t, ogtenv)
  | _ -> raise TypeError

let showet expr =
  (showe expr) ^ " : " ^ (showt (check_type expr))
let display expr = print_string (showet expr); print_newline ()

let rec show_execution' expr =
  let take_next_step () = let expr' = smallstep expr in display expr; show_execution' expr' in
  match expr with
  | Int n -> display expr
  | Bool b -> display expr
  | Lambda (e,t) -> display expr
  | _ -> take_next_step ()

let show_execution expr = show_execution' (desugar expr)

let my_test_prog = Let (Base (Int 3), Base(Var 0)) (*This is sugar for (lambda.0)0*)

let inf = Lambda (Application (Var 0, Var 0), TVar (0,false))
let _ = display inf



