open Definitions

type ('a,'s) state = 's -> ('a * 's)
let return_state x = fun s -> (x,s)
(* use this to ignore old stateful comp's result *)
let (>>=) (init_state:('a,'s) state) (transform:('b,'s) state) =
  (fun old_state ->
  let first_val, first_state = init_state old_state in
  transform first_state
  )
(* use this if you want that result *)
let (-->) (init_state:('a,'s) state) (transform:'a -> ('b,'s) state) =
  (fun old_state ->
  let first_val, first_state = init_state old_state in
  transform first_val first_state
  )

let init_name = Sub 0

let smallstep e : (expr, var_name) state =
match e with
| Int n -> return_state (Int n)
| Bool b -> return_state (Bool b)
| Plus (Int n1, Int n2) -> return_state (Int (n1 + n2))
| Plus (e1,e2) -> failwith "unimplemented"
| Times (Int n1, Int n2) -> return_state (Int (n1 * n2))
| Times (e1,e2) -> failwith "unimplemented"
| Var vname -> return_state (Var vname)
| Lambda (ebody,arg) -> failwith "unimplemented"
| Application (e1,e2) -> failwith "unimplemented"
| If (guard,e1,e2) -> failwith "unimplemented"
| Closure eref -> failwith "unimplemented"

let rec eval e : expr =
  if is_val e then e else let e' = smallstep e in eval e'
