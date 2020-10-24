open Definitions
open List
(** the [either] monad allows us to express failure in a principled way*)
type ('a,'b) either = Left of 'a | Right of 'b
let return a = Right a
let (>>=) e f =
match e with
| Left a -> Left a
| Right a -> f a
let (let*) x f = x >>= f

(* unfortunately we cannot overload the monadic operators *)
type ('a,'s) state = 's -> ('a * 's)
let return' x = fun s -> (x,s)
(* this is standard bind *) 
let (>>=^) (init_state:('a,'s) state) (transform:'a -> ('b,'s) state) =
  (fun old_state ->
  let first_val, first_state = init_state old_state in
  transform first_val first_state
  )
let (let^) x f = x >>=^ f
let state s = (s,s)

(** [info] should be line and column info *)
type info = int * int

(* [error_msg] tells what went wrong during type checking *)
type error_msg = string

let rec strip_base : typed_expr -> expr = function
| TInt n -> Int n
| TBool b -> Bool b
| TVar v -> Var v
| TPlus (e1,e2) -> Plus (strip_base e1, strip_base e2)
| TTimes (e1,e2) -> Times (strip_base e1, strip_base e2)
| TLambda (e1,v,tv) -> Lambda (strip_base e1, v)
| TApplication (e1,e2) -> Application (strip_base e1, strip_base e2)
| TIf (e1,e2,e3) -> If (strip_base e1, strip_base e2, strip_base e3)
| TEq (e1,e2) -> Eq (strip_base e1, strip_base e2) 

let rec strip : typed_sugar -> sugar = function
| TLet (v,e1,e2) -> Let (v, strip e1, strip e2)
| TLetRec (v,tv,e1,e2) -> LetRec (v, strip e1, strip e2)
| TBase e -> Base (strip_base e)

(**[venv] is the type of the variable type environment.
   Ideally this would be a map but setting this up is giving me issues so I'm starting by using an association list.
   Invariant is that keys should not appear more than once (otherwise [remove_assoc] will not remove all bindings.*)
type venv = (var_name * expr_type) list

(*
(** [add_rec_var_annotations] is a helper for [desugar_help] used to add the type annotations required by recursive definitions in the base [typed_expr] expressions contained in the top level [typed_sugar] expression *)
let rec add_rec_var_annotations texpr venv : typed_expr * venv =
let self texpr venv = fst (add_rec_var_annotations texpr venv) in
match texpr with
| TInt _ -> (texpr, venv)
| TBool _ -> (texpr, venv)
| TVar (v,_) ->
  let t_opt = assoc_opt v venv in
  (TVar (v,t_opt), venv)
| TPlus (e1,e2) ->
  let e1' = self e1 venv in
  let e2' = self e1 venv in
  (TPlus (e1', e2'), venv)
| TTimes (e1,e2) ->
  let e1' = self e1 venv in
  let e2' = self e1 venv in
  (TTimes (e1', e2'), venv)
| TLambda (e1,v,t) ->
      let venv' = remove_assoc v venv in
      let e1' = self e1 venv' in
      (TLambda (e1', v, e2'), venv) (* this part is tricky; we only want to remove the binding for `deeper` instances, so ignore the new venv after determining e1' and e2'*)
| TApplication (e1,e2) ->
  let e1' = self e1 venv in
  let e2' = self e2 venv in
  TApplication (e1',e2')
| TIf (e1,e2,e3) ->
  let e1' = self e1 venv in
  let e2' = self e2 venv in
  let e3' = self e2 venv in
  TIf (e1',e2',e3')
| TEq (e1,e2) ->
  let e1' = self e1 venv in
  let e2' = self e1 venv in
  (TEq (e1', e2'), venv)

let rec desugar_help (tsugar:typed_sugar) (venv: venv) : typed_expr = match tsugar with
| TBase e -> e
| Let (v,e1,e2) -> 

let desugar (tsugar:typed_sugar) : typed_expr = desugar_help tsugar []
*)
(* this is all commented because the work of going through and putting type annotations on all the variables before type checking is basically as much work as just type checking it to start with *)

let rec tcheck_simple : typed_expr -> (error_msg,expr_type) either = function
| _ -> failwith "unimplemented"

(** [tcheck t_expr] *)
let rec tcheck venv : typed_sugar -> (error_msg,expr_type) either = function
| TBase expr -> fun venv -> tcheck_simple expr venv
| TLet (v,e1,e2) ->
  let* tv = tcheck e1 in
  fun venv ->
    tcheck e2 ((v,tv)::venv)
| TLetRec (v,tv,e1,e2) ->
  (fun venv ->
    let venv' = (v,tv)::venv in
    let* t1 = tcheck e1 venv' in
    if t1 <> tv then Left (Prinft.sprintf "%s had declared type %s but was equated to an expression of type %s" (string_of_var v) (string_of_type tv) (string_of_type t1))
    else
    tcheck e2 venv')

  



let typecheck sugar_e =
  let* mtype = tcheck sugar_e in
  return (mtype, strip sugar_e)

