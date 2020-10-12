open Ast

exception UnboundVariable of var
exception TypeError of typename * typename * string 

show_info info = 
  match info with
  | ((l1,c1),(l2,c2)) -> "line " ^ (string_of_int l1) ^ " character " ^ (string_of_int c1) ^ " to line " ^ (string_of_int l2) ^ " character " ^ (string_of_int c2)

let mismatchmsg t1 t2 info =
  "Expression declared type " ^ t1 ^ " but it has type " ^ t2 " at " ^ (show_info info)

type vstore = var -> expr option
type tstore = typename -> typeexpr option

let empty_store x = None

type ktypes = dbvar -> typename
type tconfig = ktypes * tstore * prog


let base_types : tstore = empty_store

let make_config prog = (empty_store, base_types, prog)

let sub_in f x y = fun l -> if l = x then Just y else f c


let rec dbtcheck (conf:config) : ktypes * typename =
  match config with
  | (ktypes, sigmat, Var (v, t)) ->
    (
    match ktypes v with
    | None -> sub_in ktypes v t (*since we have no type for it, it must be free, we now declare its type*)
    | Just t' -> if t' = t then (ktypes, t) else raise TypeError of (t, t', "type error here") (*if we have a type for it, check that it matches the declaration t and raise an error if appropriate*)
    )
  | (ktypes, sigmat, Let (v, e1, e2)) ->
    match dbtcheck e1 with
    | (_,t1) -> let newktypes = sub_in ktypes v t1 in
      dbtcheck (newktypes, sigmat, e2)
  | (ktypes, sigmat, Lambda (argt, (body, bodyt))) ->
      let newktypes x = ktypes (x-1) in
      let newktypes = sub_in newktypes 0 argt in
      match dbtcheck body with
      | (_,checkbodyt) -> if checkbodyt = bodyt then
      

    
    
    
    

 (* 
and typematch t1 e2 return =
  if dbtcheck e2 = t1 then return else
  raise TypeError "types did not match"

  match conf with
  | (sigmav, sigmat, e) ->
  match e with
  | Int n -> Integer
  | Bool b -> Boolean
  | Str s -> String
  | Var (vname, tname) -> tname
  (* The lambda case must be fixed, it needs to check that the free instances of argname in bodytype have the type argtype *)
  | Lambda ((argname, argtype), (body, bodytype)) -> typematch bodytype Fun (argtype, bodytype)
  *)
