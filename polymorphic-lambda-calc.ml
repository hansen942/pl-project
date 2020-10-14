open Printf
open List
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
| Fun (t1,t2) ->
  match t1 with
  | Fun _ -> "(" ^ (showt t1) ^ ") → " ^ (showt t2)
  | _ -> (showt t1) ^ " → " ^ (showt t2)

(* For some reason ocaml is not using my error printouts I set up here. Figure out why. *)
exception FalsePolyUnkown of tvar
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

type expr_with_depth = expr * int (* need to say what the next available name is *)

let rec fill_in_annotations (ea : expr_annotated) (curr_name : int) : expr_with_depth =
match ea with
| Lambda (e, Some t) -> let sube, subcurr = fill_in_annotations e curr_name in (Lambda (sube, t), subcurr)
| Lambda (e, None) -> let sube, subcurr = fill_in_annotations e (curr_name - 1) in (Lambda (sube, TVar (curr_name, false)), subcurr)
| Application (e1,e2) -> let sube1, subcurr1 = fill_in_annotations e1 curr_name in
                         let sube2, subcurr2 = fill_in_annotations e2 curr_name in
			 (Application (sube1, sube2), min subcurr1 subcurr2)
| If (e1,e2,e3) -> let sube1, subcurr1 = fill_in_annotations e1 curr_name in
                   let sube2, subcurr2 = fill_in_annotations e2 curr_name in
		   let sube3, subcurr3 = fill_in_annotations e3 curr_name in
		   (If (sube1, sube2, sube3), min (min subcurr1 subcurr2) subcurr3)
| Plus (e1,e2) ->  let sube1, subcurr1 = fill_in_annotations e1 curr_name in
                   let sube2, subcurr2 = fill_in_annotations e2 curr_name in
		   (Plus (sube1, sube2), min subcurr1 subcurr2)
| Times (e1,e2) -> let sube1, subcurr1 = fill_in_annotations e1 curr_name in
                   let sube2, subcurr2 = fill_in_annotations e2 curr_name in
		   (Times (sube1, sube2), min subcurr1 subcurr2)
| Int n -> (Int n, curr_name)
| Var v -> (Var v, curr_name)
| Bool b -> (Bool b, curr_name)


type sugary_expr = 
| Base of expr_annotated
| Let of sugary_expr * sugary_expr 

let rec desugar_help sugary depth : expr_with_depth =
match sugary with
| Base expr -> fill_in_annotations expr depth
| Let (s1,s2) ->
  let subs1, subcurr1 = desugar_help s1 depth in
  let subs2, subcurr2 = desugar_help s2 (depth - 1) in
  (Application (Lambda (subs2, TVar (depth, false)), subs1), min subcurr1 subcurr2)

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

let rec showe_denoted_t expr =
match expr with
| Int n -> (string_of_int n) ^ " : int"
| Var v -> "v" ^ (string_of_int v)
| Lambda (e,t) -> "λ." ^ (showt t) ^ "(" ^ (showe_denoted_t e) ^ ")"
| Application (l1, l2) -> "(" ^ (showe_denoted_t l1) ^ " " ^ (showe_denoted_t l2) ^ ")"
| If (g,e1,e2) -> "if " ^ (showe_denoted_t g) ^ " then " ^ (showe_denoted_t e1) ^ " else " ^ (showe_denoted_t e2)
| Bool b -> if b then "true" else "false"
| Plus (x,y) -> (showe_denoted_t x) ^ " + " ^ (showe_denoted_t y)
| Times (x,y) -> (showe_denoted_t x) ^ " * " ^ (showe_denoted_t y)

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


type var_env = (int -> t option)
type type_scope = int list
type type_env = (int -> t option) * type_scope

(* This function gives back the TVar n's value if it is in scope *)
let tenv_access (tenv:type_env) (n:int) : t option =
  match tenv with
  | (f, scope) ->
    if mem n scope then f n else None

(* Recursively substitute an inferred type for any type variables *)
let rec update_tvars t tenv =
match t with
| Integer -> Integer
| Boolean -> Boolean
| Fun (t,t') -> Fun (update_tvars t tenv, update_tvars t' tenv)
| TVar (n,u) ->
  match tenv_access tenv n with
  | Some concrete -> concrete
  | None -> t 
type update_flag = bool

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

(* tenv, venv, name, flag *)
type state = type_env * var_env * tvar * update_flag

let tenv_access_from_state n state =
  match state with
  | (tenv,_,_,_) -> tenv_access tenv n

let updated_state state = match state with (_,_,_,flag) -> flag

(* This operator hides away some boilerplate for backtracking.
   The idea is you start in input_state and are trying to get the result of
   transform input_state in order to run you continuation but if
   transform changes the state (and so sets the flag) you need to call
   callback with callback_arg updated as is appropriate considering the
   change in state.*)
let run' (input_state:state) (transform:state -> 'a * state) (callback : 'c -> state -> 'b * state) (callback_arg : 'c) (fix_state : state -> state) (continuation : 'a -> state -> 'b * state) : 'b * state =
    let (result, new_state) = transform input_state in
    if updated_state new_state then
    match new_state with
    | (tenv, venv, _, _) ->
      callback (update_expr_annotations callback_arg tenv) (fix_state new_state)
    else continuation result input_state

let run_no_call input_state transform continuation =
    let (result, new_state) = transform input_state in
    if updated_state new_state then
    match new_state with
    | (tenv, venv, _, _) ->
      callback (update_expr_annotations callback_arg tenv) (fix_state new_state)
    else continuation result input_state

let id x = x

(* most of the time we don't need a fix_state so this is for convenience *)
let run input_state transform callback callback_arg continuation
 = run' input_state transform callback callback_arg id continuation 

(* Use this when entering a lambda to bind the 0 variable*)
let bind_var state t =
  match state with
  | (tenv,venv,name,flag) ->
    (
    let scope = snd tenv in
    let ntenv = 
    match t with
    | TVar (n,_) -> (fst tenv, n::scope)
    | _ -> tenv
    in
    (ntenv,(fun x -> if x = 0 then Some t else venv (x-1)),name,flag)
    )

exception TVarReleasedUnexpectedly

(* Use this when exiting a lambda to release the 0 variable and remove the TVar binding from the scope *)
let release_var (n: int option) state =
  match state with
  | (tenv,venv,name,flag) ->
  (* We make it the responsibility of the lambda to release its TVar from the scope *)
  let ntenv =
  match n with
  | Some n -> if hd (snd tenv) = n
              then (fst tenv, tl (snd tenv))
	      else raise TVarReleasedUnexpectedly
  | None -> tenv
  in
  (ntenv,(fun x -> if x = (-1) then None else venv (x+1)),name,flag)

(* How we type variables *)
let var_rule v state : t =
  match state with
  | (_,venv,_,_) ->
    (match venv v with
      | None -> raise UnboundVariable
      | Some t -> t
     )

(* Used to note that changes were made *)
let set_flag state : state =
  match state with
  | (tenv,venv,name,flag) -> (tenv,venv,name,true)

exception WhyYaCallin

(* this function updates the venv so that type variables pointint to type variables do not happen. Only does one layer of updates. If flag is not set then there should be no updates so does nothing.*)
let update_venv state : state =
  match state with
  | (tenv,venv,name,flag) -> 
    let updated_venv x = match venv x with
    | Some (TVar (n,u)) ->
      (
      match tenv_access tenv n with
      | Some other_t -> Some other_t
      | None -> Some (TVar (n,u)) 
      )
    | other -> other
    in
    if not flag then raise WhyYaCallin else (tenv, updated_venv, name, flag) 

(* Updates tenv n to Some t and then updates venv using update_venv *)
let set_tvar n t state : state =
  match state with
  | (tenv,venv,name,flag) ->
  let ntenv1 = fun x -> if x = n then Some t else (fst tenv) x in
  update_venv ((ntenv1, snd tenv), venv, name, true)

(* Grabs the next name available and increments the name counter in state *)
let new_type state : t * state =
  match state with
  | (tenv,venv,name,flag) -> (TVar(name,false),(tenv,venv,name-1,flag))

exception RangeTypeMissing

(* the actual type checker *)
let rec tcheck (expr:expr) (curr_state:state) : t * state =
    match expr with
    | Int _ -> (Integer, curr_state)
    | Bool _ -> (Boolean, curr_state)
    | Var v -> (var_rule v curr_state, curr_state)
    | If (b,e1,e2) -> run curr_state (constrain b Boolean) tcheck expr
      (fun _ -> fun state ->
        run state (tcheck e1) tcheck expr
	  (fun t1 -> fun state ->
	  run state (constrain e2 t1) tcheck expr
	    (fun _ -> fun state ->
	    (t1,state)
	    )
	  )
      )
    | Lambda (body,argt) ->
      let new_bind = match argt with TVar (n,_) -> Some n | _ -> None in
      run' (bind_var curr_state argt) (tcheck body) tcheck expr (release_var new_bind)
        (fun bodyt -> fun state ->
	  (Fun(argt, bodyt), release_var new_bind state)
	)
    | Application (e1,e2) ->
      run curr_state (tcheck e2) tcheck expr
        (fun t2 -> fun state ->
	  let (range_type,new_state) = new_type state in
	  run new_state (constrain e1 (Fun(t2, range_type))) tcheck expr
	  (fun _ -> fun state ->
	    match range_type with
	    | TVar (n,_) -> (match tenv_access_from_state n state with
	                       | Some t -> (t,state)
			       | None -> raise RangeTypeMissing
	                    )
	  )
	)
      
(* This function is used when expression e must have type t. *)
and constrain (e:expr) (t:t) (state:state) : unit * state =
  let te = fst (tcheck e state) in
  constrain_help te t state

and constrain_help te t state =
  if te = t then ((), state) else
  match te with
  | TVar (en,u) -> if u then raise (FalsePolymorphism (en,t))
                        else ((), set_tvar en t state)
  (* Handle the inductive case by constraining the range and domain to be the same for both *)
  | Fun (te1,te2) ->
    match t with
    | Fun (t1,t2) -> 
      run state (constrain_help te1 te2) (fun _ -> raise TypeError) ()
      (fun _ -> fun state ->
        run state (constrain_help te2 t2) (fun _ -> raise TypeError) ()
	(fun _ -> fun state -> ((), state))
      )
    | TVar _ -> constrain_help t te state
    | _ -> raise TypeError
  | _ -> constrain_help t te state

let empty = (fun x -> None)
let check_type expr_with = match expr_with with
  | (expr, start_name) -> fst (tcheck expr ((empty,[]),empty,start_name,false))


(*
(* Our type checker *)
(* venv is used to keep track of the known types of variables while tenv keeps track of hte known types of type variables
The point of also having ogtenv is that ogtenv is not updated when we infer a type from the left term of an application, and so can be
used to evaluate the type of the right term. It is necessary so that type-name-conflicts between a function
and its argument do not cause issues. These issues could arise from an application e1 e2 where we type check e1, then type check e2 which causes feedback,
and then callback on e1 e2 but the type check from e2 now impacts type variables of e1 which just happen to be the same name as those in e2, which then impacts the type check of e1.
Invariant: ogtenv = tenv at the beginning of tcheck unless the expression being evaluated is an application*)
(* when you call tcheck on a subexpression you need to check if the flag is set in the feedback it returns, if it is then it has inferred some types so you have to infer them as well*)
(* If it does infer a type, then you update your tenv then call yourself on the exact expression you were called on but with the updated tenv, you then pass the feedback back up*)
(* Raises a TypeError if any type error occurs (currently with no info).
   Raises a FalsePolymorphism error if a user annotated type variable can be inferred (i.e. if it cannot actually be any type)*)
(* TODO: fix this so it doesn't overflow *)
let rec tcheck expr venv tenv ogtenv next_name in_app : t * feedback =
(*let _ = Printf.printf "Current evaluating the expression (%s)" (showe expr); print_newline () in*)
let verify = verify_type in_app in
let no_feedback = (venv,tenv,ogtenv,next_name,false) in
match expr with
| Bool _ -> (Boolean, no_feedback)
| Int _ -> (Integer, no_feedback)
| If (guard,first,second) -> let t2 = check_type (second,next_name) in let feedback = no_feedback >> (verify guard Boolean) >> (verify first t2) in
  callback (t2,feedback) expr in_app
| Plus (x,y) -> print_string "evaluating plus "; print_newline (); let feedback = no_feedback >> (verify x Integer) >> (verify y Integer) in callback (Integer,feedback) expr in_app
| Times (x,y) -> let feedback = no_feedback >> (verify x Integer) >> (verify y Integer) in callback (Integer,feedback) expr in_app
| Var v -> (match venv v with Some t -> (t, no_feedback) | _ -> raise UnboundVariable)
| Lambda (e,t) -> handle_lambda e t venv tenv ogtenv next_name in_app
| Application (e1, e2) -> handle_application expr e1 e2 venv tenv ogtenv no_feedback next_name in_app

and handle_application expr e1 e2 venv tenv ogtenv no_feedback next_name in_app : t * feedback=
  let _ = Printf.printf "Working on %s" (showe expr); print_newline () in
  let f x = match tenv x with None -> "none" | Some x -> showt x in
  let g x = match venv x with None -> "none" | Some x -> showt x in
  let _ = Printf.printf "Currently have type mapping t(-2) -> %s t(-1) -> %s t0 -> %s t1 -> %s" (f(-2)) (f(-1)) (f 0) (f 1); print_newline () in
  let _ = print_string ("in_app = " ^ (string_of_bool in_app)); print_newline() in
  (*let _ = match venv 0 with None -> () | Some x -> Printf.printf "Currently have type (%s) for v0." (showt x) in*)
  let (t1,(venv1,tenv1,ogtenv1,next_name1,flag1)) = tcheck e1 venv tenv ogtenv next_name true in
  if flag1 then callback (t1,(venv,tenv1,ogtenv1,next_name1,flag1)) expr in_app else
  let _ = Printf.printf "Currently have t1 = %s" (showt t1); print_newline () in
  let _ = Printf.printf "Currently have type(v1) = %s" (g 1); print_newline () in
  match t1 with (* NOTE: room for efficiency improvement because we always call tcheck on e1 even if we have already determined its type and are working on e2, could pass flag*)
  | Fun(t,t') ->
  (let _ = print_string "in the concrete function case"; print_newline () in
  let (t2, (subvenv2, subtenv2, subogtenv2,subnext_name2, flag2)) = tcheck e2 venv ogtenv ogtenv next_name false in
    if flag2 then callback (t2,(subvenv2, tenv, subogtenv2,subnext_name2, flag2)) expr in_app else (* concerned about which venv we are calling back with *)
    let _ = Printf.printf "type checking e2 succeeded in producing type %s" (showt t2); print_newline () in
    match t with
    | TVar (n,u) ->
      (match tenv n with
      | Some tknown -> if tknown = t2 then (update_tvars t' tenv, (venv1,tenv1,ogtenv1,next_name1,flag1))
	else callback (t', (venv, update_tenv tenv n t2, ogtenv, next_name, true)) expr in_app
      | None -> let new_tenv x = if x = n then Some t2 else tenv x in
      tcheck (Application (e1,e2)) venv new_tenv tenv next_name in_app
      )
    | _ -> if t2 = t then (print_string "succceeded in matching argument type to argument"; print_newline (); (t', (venv,tenv,ogtenv,next_name,in_app))) else raise TypeError (* We give feedback if in application because we may have updated a type variable bound higher up *)
    )
  | TVar (x,_) ->
    let feedback = (venv,tenv,ogtenv,next_name-2,false)
    >> (verify_type in_app e1 (Fun(TVar(next_name,false), TVar(next_name - 1,false)))) in
    let _ = Printf.printf "Currently found I'm applying a Tvar with new type for t(%i) -> (%s)" x (f x) in callback (TVar(next_name-1,false),feedback) expr in_app
  | _ -> raise TypeError

(* helper to call type checker more easily *)
and check_type exp = match exp with
  | (exp, curr_name) -> fst (tcheck exp (fun x -> None) (fun x -> None) (fun x -> None) curr_name false)
(*and check_type (exp : expr_with_depth) : t = fst (check_type_verbose expr)*)

(* used to automate calling oneself and sending feedback up*)
(* usually we want to set ogtenv = tenv before doing the call back so that it stays up-to-date as we descend into the tree,
   however this must be avoided if we are working on an application because that would defeat the whole point of having ogtenv*)
and callback output self in_app : t * feedback =
  let equateog = match self with
  | Application _ -> false
  | _ -> true
  in
  match output with
  | (t, (venv, tenv, ogtenv, next_name, flag)) ->
  if flag && ((not in_app) || (not equateog)) then
    ((*Printf.printf "Called back to expression (%s)" (showe self); print_newline ();
    Printf.printf "Found type was (%s)" (showt t); print_newline ();*)
    let updated_self =
      (match self with
      | Application (e1,e2) -> Application (update_expr_annotations e1 tenv, update_expr_annotations e2 ogtenv)
      | _ -> update_expr_annotations self tenv
      )
     in
    let ogtenv = if equateog then tenv else ogtenv in
    match tcheck updated_self venv tenv ogtenv next_name in_app with
    | (t,(subvenv,subtenv,subogtenv,subnext_name,subflag)) -> (t,(update_venv subvenv subtenv,subtenv,subogtenv,subnext_name,true)))
  else (t, (venv, tenv, ogtenv, next_name, flag))

and handle_lambda e t venv tenv ogtenv next_name in_app : t * feedback =
  let new_venv x = if x = 0 then Some t else venv (x-1) in
  match tcheck e new_venv tenv tenv next_name in_app with (* here we have replaced ogtenv with tenv, idea being that if you are entering a lambda then you're not in an application *)
  | (te,(nvenv,ntenv,nogtenv,nnext_name,flag)) ->
    if flag then
    let nt = update_tvars t ntenv in
    (*as going outside the lambda have to shift the variables*)
    let outside_venv x = if not (x = (-1)) then venv (x+1) else None in
    (Fun (nt, te), (outside_venv,ntenv,nogtenv,nnext_name,flag)) 
    else (Fun (t,te), (venv,tenv,ogtenv,next_name,flag)) (* the data in this feedback is not valid so should not be used, its flag is false though so this should be fine *)

(* this function checks that echeck has type t in the given contexts;
if it does not then it checks if it is polymorphic, if so it updates the type environments and returns them, otherwise it throws a TypeError *)
and verify_type in_app echeck t venv tenv ogtenv next_name : (type_env * type_env * type_env * tvar) option =
  let (tfound, (subvenv, subtenv, subogtenv, next_name, flag)) = tcheck echeck venv tenv ogtenv next_name in_app in
  if tfound = t then (if not flag then None else Some (subvenv, subtenv, subogtenv, next_name))
  else
  match tfound with
  | TVar (n,u) ->
  if u then raise (FalsePolymorphism (n,t)) else
  let new_tenv = update_tenv subtenv n t in Some (update_venv venv new_tenv, update_tenv subtenv n t, ogtenv, next_name)
  | _ -> raise TypeError
*)
let showet expr_with =
  match expr_with with (expr, name) ->
  (showe expr) ^ " : " ^ (showt (check_type expr_with))
let display expr = print_string (showet expr); print_newline ()

let rec show_execution' expr_with =
  match expr_with with
  | (expr, name) ->
  let take_next_step () = let expr' = smallstep expr in display expr_with; show_execution' (expr', name) in
  match expr with
  | Int n -> display expr_with; print_newline (); print_string (showe_denoted_t expr)
  | Bool b -> display expr_with; print_newline (); print_string (showe_denoted_t expr)
  | Lambda (e,t) -> display expr_with; print_newline (); print_string (showe_denoted_t expr)
  | _ -> take_next_step ()


let bare_expr expr_with = match expr_with with (expr,name) -> expr

let show_execution expr = show_execution' (desugar expr)

let my_test_prog = Let (Base (Int 3), Base(Var 0)) (*This is sugar for (lambda.0)0*)
(*let _ = display (desugar my_test_prog)*)
let simple_if = (Lambda(If(Var 0, Int 1, Int 0), Boolean),-1)

let add_to_if = (Lambda (Lambda (Plus(Var 0, Application(Var 1, Bool true)), Integer), Fun(Boolean, Integer)),-1)

let poly_if = (Lambda(If(Var 0, Int 1, Int 0), TVar (0,false)),-1)
let poly_add_if = (Lambda (Lambda (Plus(Var 0, Application(Var 1, Bool true)), TVar(0,false)), TVar (1,false)),-1)

let _ = display ( Application (fst poly_add_if, fst poly_if), (-1))






