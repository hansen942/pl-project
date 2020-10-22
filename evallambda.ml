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

let init_name = Sub 0

type eval_state = var_name
(** [let*] gives us some noice syntax similar to [do] notation in Haskell*)
let (let*) x f = x >>= f
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
  failwith "unimplemented"
  (*TODO: this needs to get new variable names or something like that *)
  | Z -> subin z
  | Eq (e1,e2) ->
    let* e1' = subin e1 in
    let* e2' = subin e2 in
    return (Eq (e1',e2'))

let rec smallstep e : (expr, eval_state) state =
print_string (string_of_expr e); print_newline (); print_newline ();
match e with
| Z -> return z
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

(*and map_state (lst:'a list) (f: 'a -> ('b,'s) state) : ('b list, 's) state =
  fold_right (fun x acc ->
  let* x' = f x in
  let* acc' = acc in
  return (x'::acc')) lst (return []) 
*)

(*
| If (guard,e1,e2) -> failwith "unimplemented"
| Times (Int n1, Int n2) -> return (Int (n1 * n2))
| Times (e1,e2) -> failwith "unimplemented"
*)

let rec eval' e s =
  if is_val e then e else let e', s' = smallstep e s in eval' e' s'

let eval e : expr = eval' e init_name
