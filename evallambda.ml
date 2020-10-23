open Definitions
open List

type ('a,'s) state = 's -> ('a * 's)
let return x = fun s -> (x,s)
(* this is standard bind *) 
let (>>=) (init_state:('a,'s) state) (transform:'a -> ('b,'s) state) =
  (fun old_state ->
  let first_val, first_state = init_state old_state in
  transform first_val first_state
  )
(* use this if you want to throw away first computations result *)
let (-->) (init_state:('a,'s) state) (transform: ('b,'s) state) =
  (fun old_state ->
  let first_val, first_state = init_state old_state in
  transform first_state
  )

(** [let*] gives us some noice syntax similar to [do] notation in Haskell*)
let (let*) x f = x >>= f

type eval_state = var_name

let init_name : eval_state = Sub 0

(** [draw_name] gives back the next free name and updates the state *)
let draw_name : (var_name, eval_state) state =
  fun s -> match s with
  | Sub n -> (s,Sub (n+1))
  | _ -> failwith "evaluation state corrupted, unable to draw name"

let rec naive_list_union' acc l1 = function
| h::t -> if mem h l1 then naive_list_union' acc l1 t else naive_list_union' (h::acc) l1 t
| [] -> acc @ l1

(** [list_union l1 l2] is a list that contains all the elements of [l1] and [l2] with no repeats, assuming that [l1] and [l2] also contain no repeats.
    Also note this is not tail recursive (because of use of [@] operator) and will have recursion depth = length of [l2]*)
let naive_list_union = naive_list_union' []

(** [fv e] gives a list containing all the free variables of [e].
    Ideally, we would replace the list with a set but this requires defining an order on expressions so I'm just building it with lists first.*)
let rec fv : expr -> var_name list = function
| Int _ -> []
| Var v -> [v]
| Lambda (ebody,arg) -> filter (fun x -> not (x = arg)) (fv ebody)
| Application (e1,e2) -> naive_list_union (fv e1) (fv e2)
| If (e1,e2,e3) -> naive_list_union (fv e1) (naive_list_union (fv e2) (fv e3))
| Bool _ -> []
| Plus (e1,e2) -> naive_list_union (fv e1) (fv e2)
| Times (e1,e2) -> naive_list_union (fv e1) (fv e2)
| Eq (e1,e2) -> naive_list_union (fv e1) (fv e2)


(** [sub e e_x x] gives back [e] with free occurrences of [x] replaced by [e_x].*)
let rec sub e e_x x : (expr, eval_state) state =
  let subin e = sub e e_x x in
  match e with
  | Application (e1,e2) ->
    let* e1' = subin e1 in
    let* e2' = subin e2 in
    return (Application (e1',e2'))
  | Var v -> if v = x then return e_x else return e
  | If (e1,e2,e3) ->
    let* e1' = subin e1 in
    let* e2' = subin e2 in
    let* e3' = subin e3 in
    return (If (e1',e2',e3'))
  | Plus (e1,e2) ->
    let* e1' = subin e1 in
    let* e2' = subin e2 in
    return (Plus (e1',e2'))
  | Times (e1,e2) ->
    let* e1' = subin e1 in
    let* e2' = subin e2 in
    return (Times (e1',e2'))
  | Bool _ -> return e 
  | Int _ -> return e
  | Lambda (body,arg) ->
  if arg = x then return e else
    if not(mem arg (fv e_x)) then
      (* This case is standard *)
      let* body' = subin body in
      return (Lambda (body',arg))
    else
      (* In this case a free variable of e_x would become bound. To avoid this we draw a new argument name, then substitute all the free occurrences of the old argument name in the body out for the new argument name *)
      let* new_arg_name = draw_name in
      let* new_body = sub body (Var new_arg_name) arg in
      let* new_body' = subin new_body in
      return (Lambda (new_body',new_arg_name))
  (*TODO: this needs to replace the arg with a new variable if arg \in fv(e_x) and fix body before substituting *)
  | Eq (e1,e2) ->
    let* e1' = subin e1 in
    let* e2' = subin e2 in
    return (Eq (e1',e2'))

and smallstep e : (expr, eval_state) state =
match e with
| Application (Lambda (e1,x),e2) ->
  if not (is_val e2)
  then let* e2' = smallstep e2 in
    return (Application (Lambda (e1,x),e2'))
  else sub e1 e2 x
| Application (e1,e2) ->
  let* e1' = smallstep e1 in
  return (Application (e1', e2))
| Plus (Int n1, Int n2) -> return (Int (n1 + n2))
| Plus (e1,e2) ->
  let* e1' = smallstep e1 in
  let* e2' = smallstep e2 in
  return (Plus (e1', e2'))
| Times (Int n1, Int n2) -> return (Int (n1 * n2))
| Times (e1,e2) ->
  let* e1' = smallstep e1 in
  let* e2' = smallstep e2 in
  return (Times (e1', e2'))
| If (Bool b,e2,e3) -> if b then return e2 else return e3
| If (e1,e2,e3) ->
  let* e1' = smallstep e1 in
  return (If (e1',e2,e3))
| Eq (Int n1, Int n2) -> return (Bool (n1 = n2))
| Eq (Bool b1, Bool b2) -> return (Bool (b1 = b2))
| Eq (e1,e2) ->
  let* e1' = smallstep e1 in
  let* e2' = smallstep e2 in
  return (Eq (e1',e2'))
| Int _ -> return e
| Bool _ -> return e
| Lambda _ -> return e
| Var _ -> return e


let rec eval' e s =
  if is_val e then e else
  let e', s' = smallstep e s in eval' e' s'

let eval e : expr = eval' e init_name

(* This small test case checks sub *)
(*
let test_sub_e = Lambda (Var (Name "y"), Name "x")
let _ = Printf.printf "%s {x / y} = %s" (string_of_expr test_sub_e) (string_of_expr (fst (sub test_sub_e (Var (Name "x")) (Name "y") init_name))); print_newline ()
*)


