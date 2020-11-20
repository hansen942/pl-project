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
  | Unit -> return Unit
  | Print e -> let* e' = subin e in return (Print e')
  | Prod elist ->
    let* elist' = fold_right (fun x acc -> let* x' = subin x in let*acc' = acc in return(x'::acc')) elist (return []) in
    return (Prod elist')
  | Proj(e,n) -> let* e' = subin e in return(Proj(e',n))

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
| Match(e,matches) ->(
  match e with
  | Sum (uname,e) ->
    match assoc_opt uname matches with
    | None -> failwith (Printf.sprintf "match failed, no case for %s" uname)
    | Some f -> return (Application(f,e))
  | _ -> failwith (Printf.sprintf "cannot match on %s, it is not a sum type" (string_of_expr e))
  )
| Proj(e,n) ->(
  match e with
  | Prod elist ->(
    match nth_opt elist n with
    | None -> failwith "index out of bounds"
    | Some e' -> return e'
    )
  | _ -> failwith "cannot project an expression that is not a product"
)
| Int _ -> return e 
| Bool _ -> return e 
| Lambda _ -> return e 
| Var _ -> return e  
| Unit -> return e 
| Print e -> fun s -> print_endline (string_of_expr (eval' e s)); (Unit,s)
| Sum (c,e) -> let* e' = smallstep e in return (Sum (c,e'))
| Prod elist ->
  let* elist' = fold_right (fun x acc -> let* x' = smallstep x in let* acc' = acc in return(x'::acc')) elist (return []) in
  return (Prod elist')


and eval' e s =
  if is_val e then e else
  let e', s' = smallstep e s in eval' e' s'

let eval e s : expr = eval' e s 

(* This small test case checks sub *)
(*
let test_sub_e = Lambda (Var (Name "y"), Name "x")
let _ = Printf.printf "%s {x / y} = %s" (string_of_expr test_sub_e) (string_of_expr (fst (sub test_sub_e (Var (Name "x")) (Name "y") init_name))); print_newline ()
*)


