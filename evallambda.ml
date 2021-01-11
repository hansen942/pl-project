open Definitions
open List



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
  | Bool _ -> return e 
  | Int _ -> return e
  | Float _ -> return e
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
  | Unit -> return Unit
  | Print e -> let* e' = subin e in return (Print e')
  | Prod elist ->
    let* new_elist = state_fmap subin elist in
    return (Prod new_elist) 
  | Proj(e,n) -> let* e' = subin e in return(Proj(e',n))
  | Match(e,cases) ->
    let* e' = subin e in
    let* cases' = state_fmap (fun (case_name,case_handler) -> let* new_handler = subin case_handler in return (case_name,new_handler)) cases in
    return(Match(e',cases'))
  | Sum(cons,e) ->
    let* e' = subin e in
    return(Sum(cons,e'))
  | Binop (e1,op,e2) ->
    let* e1' = subin e1 in
    let* e2' = subin e2 in
    return (Binop (e1',op,e2'))
  | Neg e -> let* e' = subin e in return (Neg e')
  | Stub -> return Stub

and do_binop op e1 e2 =
  if (not (is_val e1)) || (not (is_val e2)) then
  failwith "internal error: not supposed to use do_binop on non values"
  else
  match e1,e2 with
  | Int n1, Int n2 -> (
    match op with
    | Plus -> Int (n1 + n2)
    | Times -> Int (n1 * n2)
    | L -> Bool (n1 < n2)
    | G -> Bool (n1 > n2)
    | Eq -> Bool (n1 = n2)
    | Mod ->
      if n2 = 0 then Sum("None",Unit) else
      Sum("Some",Int (let maybe_result = n1 mod n2 in if maybe_result < 0 then maybe_result + n2 else maybe_result))
    | Subtract -> Int (n1 - n2)
    | Div ->(
      try let q = n1 / n2 in
      Sum("Some", Int q)
      with _ -> Sum("None",Unit)
    )
    | _ -> failwith "failed in do_binop"
    )
  | Float n1, Float n2 -> (
    match op with
    | Plus -> Float (n1 +. n2)
    | Times -> Float (n1 *. n2)
    | L -> Bool (n1 < n2)
    | G -> Bool (n1 > n2)
    | Eq -> Bool (n1 = n2)
    | Subtract -> Float (n1 -. n2)
    | Div ->(
      try let q = n1 /. n2 in
      Sum("Some",Float q)
      with _ -> Sum("None",Unit)
    )
    | _ -> failwith "failed in do_binop"
    )
  | Bool b1, Bool b2 -> (
    match op with
    | Eq -> Bool (b1 = b2)
    | And -> Bool (b1 && b2)
    | Or -> Bool (b1 || b2)
    | _ -> failwith "failed in do_binop"
    )
  | _ -> ( 
    match op with
    | Eq -> (
      match e1, e2 with
      | Sum (cons1,e1), Sum (cons2,e2) ->
      if cons1 <> cons2 then Bool false else
        Binop(e1,Eq,e2)
      | Prod elist, Prod elist' ->
        (* safe because will have been type checked so should be of same length *)
        let must_hold_list = combine elist elist' in
	(* turn into component-wise equalities *)
	fold_left (fun acc (x,y)-> Binop(Binop(x,Eq,y),And,acc)) (Bool true) must_hold_list
      | _ -> failwith "failed in do_binop"
      )
    | _ -> failwith (Printf.sprintf "failed in do_binop, given %s %s %s" (string_of_expr e1) (string_of_binop op) (string_of_expr e2))
    )

(** [smallstep e] gives back the expression that [e] (small) steps to. For convenience this function just returns its input if it is given a value.*)
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
| If (Bool b,e2,e3) -> if b then return e2 else return e3
| If (e1,e2,e3) ->
  let* e1' = smallstep e1 in
  return (If (e1',e2,e3))
| Match(e,matches) ->(
  match e with
  | Sum (uname,e) ->
    (match assoc_opt uname matches with
    | None -> failwith (Printf.sprintf "match failed, no case for %s" uname)
    | Some f -> return (Application(f,e)))
  | _ -> let* e' = smallstep e in return(Match(e',matches))
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
| Neg e -> if is_val e then
  match e with
  | Int n -> return(Int (-n))
  | Float f -> return(Float (-.f))
  | _ -> failwith "runtime type error"
  else let* e' = smallstep e in return(Neg e')
| Binop (e1,op,e2) -> if is_val e1 && is_val e2 then return(do_binop op e1 e2) else
  let* e1' = smallstep e1 in
  let* e2' = smallstep e2 in
  return(Binop(e1',op,e2'))
| Int _ -> return e 
| Float _ -> return e
| Bool _ -> return e 
| Lambda _ -> return e 
| Var _ -> failwith "cannot evaluate a variable"
| Unit -> return e 
| Print e -> fun s -> print_endline (string_of_expr (eval' e s)); (Unit,s)
| Sum (c,e) -> let* e' = smallstep e in return (Sum (c,e'))
| Prod elist ->
  let* elist' = fold_right (fun x acc -> let* x' = smallstep x in let* acc' = acc in return(x'::acc')) elist (return []) in
  return (Prod elist')
| Stub -> failwith "tried to evaluate an unimplemented statement"


and eval' e s =
  if is_val e then e else
  let e', s' = smallstep e s in eval' e' s'

(** [eval e] gives the value that [e] evaluates to. Will never terminate if [e] does not terminate. *)
let eval e init_name : expr = eval' e init_name
