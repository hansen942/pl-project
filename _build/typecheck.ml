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
| TUnit -> Unit
| TPrint e -> Print (strip_base e)
| TSum (name,e) -> Sum(name,strip_base e)
| TProd elist -> Prod(map strip_base elist)
| TMatch (e,cases) -> Match (strip_base e, map (fun (c,e) -> (c,strip_base e)) cases)
| TProj (e,n,l) -> Proj (strip_base e, n)

let rec strip : typed_sugar -> sugar = function
| TLet (v,e1,e2) -> Let (v, strip e1, strip e2)
| TLetRec (v,tv,e1,e2) -> LetRec (v, strip e1, strip e2)
| TBase e -> Base (strip_base e)

(**[venv] is the type of the variable type environment.
   Ideally this would be a map but setting this up is giving me issues so I'm starting by using an association list.
   Invariant is that keys should not appear more than once (otherwise [remove_assoc] will not remove all bindings.*)
type venv = (var_name * expr_type) list
type user_type_env = (user_var_name * expr_type) list

let undeclared_error v =  Printf.sprintf "The variable %s is undeclared" (string_of_var v)
let inferred_mismatch e t reason found = Printf.sprintf "Expression %s was expected to have type %s because %s but its actual type is %s" (string_of_typed_expr e) (string_of_type t) reason (string_of_type found)
let declared_mismatch_error v declared got = Printf.sprintf "%s had declared type %s but was equated to an expression of type %s" (string_of_var v) (string_of_type declared) (string_of_type got)

(*Note: this has not been updated to deal with sums and products *)
(*
let rec tcheck_simple venv : typed_expr -> (error_msg,expr_type) either = function
| TInt _ -> return Integer 
| TBool _ -> return Boolean 
| TVar v -> (match assoc_opt v venv with Some t -> return t | None -> Left (undeclared_error v))
| TPlus (e1,e2) ->
  let* t1 = tcheck_simple venv e1 in
  let* t2 = tcheck_simple venv e2 in
  if t1 != Integer then Left (inferred_mismatch e1 Integer "it appears in a plus formula" t1) else
  if t2 != Integer then Left (inferred_mismatch e2 Integer "it appears in a plus formula" t2) else
  return Integer
| TTimes (e1,e2) ->
  let* t1 = tcheck_simple venv e1 in
  let* t2 = tcheck_simple venv e2 in
  if t1 <> Integer then Left (inferred_mismatch e1 Integer "it appears in a plus formula" t1) else
  if t2 <> Integer then Left (inferred_mismatch e2 Integer "it appears in a plus formula" t2) else
  return Integer
| TLambda (e,v,tv) ->
  let venv' = (v,tv)::venv in
  let* tbody = tcheck_simple venv' e in
  return (Fun(tv,tbody))
| TApplication (e1,e2) ->
  let* t1 = tcheck_simple venv e1 in
  let* t2 = tcheck_simple venv e2 in
  (match t1 with
  | Fun (targ,treturn) ->
    (
      if targ <> t2 then Left (inferred_mismatch e2 targ (Printf.sprintf "it is given as an argument to %s which has type %s" (string_of_typed_expr e1) (string_of_type t1)) t1)
      else return treturn
    )
    | _ -> Left (Printf.sprintf "%s is not a function (it has type %s), it cannot be applied" (string_of_typed_expr e1) (string_of_type t1))
  )
| TIf (e1,e2,e3) ->
  let* t1 = tcheck_simple venv e1 in
  let* t2 = tcheck_simple venv e2 in
  let* t3 = tcheck_simple venv e3 in
  if t1 <> Boolean then Left (inferred_mismatch e1 Boolean "it appears in the guard of an if expression" t1)
  else if t2 <> t3 then Left (inferred_mismatch e3 t2 (Printf.sprintf "it appears as an alternative outcome to %s : %s in an if expression" (string_of_typed_expr e2) (string_of_type t2)) t3)
  else return t2
| TEq (e1,e2) ->
  let* t1 = tcheck_simple venv e1 in
  let* t2 = tcheck_simple venv e2 in
  if t1 <> t2 then Left (inferred_mismatch e2 t1 (Printf.sprintf "it is compared to %s : %s" (string_of_typed_expr e1) (string_of_type t1)) t2)
  else return Boolean
| TUnit -> return UnitType
| TPrint e ->
  let* t = tcheck_simple venv e in
  if printable t then return UnitType else Left (Printf.sprintf "Expected %s to be a printable expression, as it appears in a print statement, but it has type %s" (string_of_typed_expr e) (string_of_type t))
*)


type tconstraint =
| Equality of expr_type * expr_type
| TypeClass of expr_type * type_class
type constraints = tconstraint list

let string_of_tconstraint = function
| Equality (t1,t2) -> Printf.sprintf "%s = %s" (string_of_type t1) (string_of_type t2)
| TypeClass (t,c) -> Printf.sprintf "%s = %s" (string_of_type t) (string_of_typeclass c)

let string_of_constraints =
fold_left (fun acc x -> acc ^ "\n" ^ (string_of_tconstraint x)) ""


let constrain t1 t2 _ (constraints,name) = ((),((Equality (t1,t2))::constraints,name))
let class_constrain t1 c _ (constraints,name) = ((),((TypeClass (t1,c))::constraints,name))
let ignore f = fun _ -> f

let init_name : var_name = Sub 0

(** [draw_name] gives back the next free name and updates the state *)
let draw_name : (var_name,constraints * var_name) state = function
  | (c,Sub n) -> (Sub n,(c,Sub (n+1)))
  | _ -> failwith "type variable source corrupted, unable to draw name"

let rec tcheck_simple' venv : typed_expr -> (expr_type,constraints * var_name) state = function
| TInt _ -> return' Integer
| TBool _ -> return' Boolean
| TVar v -> (match assoc_opt v venv with
             | Some t -> return' t
	     | None -> failwith (undeclared_error v))
| TPlus (e1,e2) ->
  let^ t1 = tcheck_simple' venv e1 in
  let^ t2 = tcheck_simple' venv e2 in
  constrain t1 Integer () >>=^ constrain t2 Integer >>=^ ignore(return' Integer)
| TTimes (e1,e2) ->
  let^ t1 = tcheck_simple' venv e1 in
  let^ t2 = tcheck_simple' venv e2 in
  constrain t1 Integer () >>=^ constrain t2 Integer >>=^ ignore(return' Integer)
| TLambda (e,v,tv) ->
  let venv' = (v,tv)::venv in
  let^ tbody = tcheck_simple' venv' e in
  return' (Fun(tv,tbody))
| TApplication (e1,e2) ->
  let^ t1 = tcheck_simple' venv e1 in
  let^ t2 = tcheck_simple' venv e2 in
  let^ new_name = draw_name in
  constrain t1 (Fun(t2,TypeVar new_name)) () >>=^ ignore(return' (TypeVar new_name))
| TIf (e1,e2,e3) ->
  let^ t1 = tcheck_simple' venv e1 in
  let^ t2 = tcheck_simple' venv e2 in
  let^ t3 = tcheck_simple' venv e3 in
  constrain t1 Boolean () >>=^ constrain t2 t3 >>=^ ignore (return' t2)
| TEq (e1,e2) ->
  let^ t1 = tcheck_simple' venv e1 in
  let^ t2 = tcheck_simple' venv e2 in
  constrain t1 t2 () >>=^ ignore(return' Boolean)
| TUnit -> return' UnitType
| TPrint e ->
  let^ t = tcheck_simple' venv e in
  class_constrain t (Printable) () >>=^ ignore(return' UnitType)
| TSum (cons,texpr) ->
  (*TODO: to get this case, we need to add an environment of defined sum types so that we verify the constructor exists and find the associated sum type *)
  failwith "unimplemented"
| TProd elist ->
  let^ tlist = fold_right (fun x acc -> let^ t_new = tcheck_simple' venv x in let^ acc' = acc in return' (t_new::acc')) elist (return' []) in
  return' (Product tlist)
| TMatch (e,cases) ->
  (* not much point implementing this when we don't have sums yet.
     of course we will check that e is a sumtype and the cases are
     constructors of that type, and that the return type of all the functions
     are equal*)
  failwith "unimplemented"
| TProj (e,n,l) ->
  (* note we zero index *)
  if n >= l || n < 0 then failwith "index out of bounds" else
  if l < 0 then failwith "projections not defined for tuples of negative length" else
  (* generate a generic type for product of length l and constrain e to have this type *)
  let rec make_gen_prod' so_far_done tlist_so_far l =
    if so_far_done = l then return' tlist_so_far else
    let^ t_new = draw_name in make_gen_prod' (so_far_done + 1) ((TypeVar t_new)::tlist_so_far) l
    in
  let make_gen_prod l = let^ tlist = make_gen_prod' 0 [] l in return' ((Product tlist),nth tlist n) in
  let^ gen_prod,t_out = make_gen_prod l in
  let^ te = tcheck_simple' venv e in
  constrain te gen_prod () >>=^ ignore(return' t_out)



let tcheck_simple'' venv typed_expr : expr_type * constraints =
  let out = tcheck_simple' venv typed_expr ([],init_name) in
  (fst out, fst (snd out))


let update_sub sub1 sub2 =
map (fun x -> match x with (t,t') ->
  (match t' with
  | TypeVar v ->
    (match assoc_opt v sub2 with
    | None -> (t,t')
    | Some t'' -> (t,t''))
  | _ -> (t,t')
  )
  ) sub1

(*[sub_comp sub2 sub1] gives back the composite map sub2 \circ sub1.
  Precondition: The domains of sub1 and sub2 are disjoint*)
let sub_comp sub2 sub1 =
  let sub1_new = update_sub sub1 sub2 in
  sub2 @ sub1_new

(* used to substitute into all the type equations.
   We don't touch the typeclass constraints because
   these are just supposed to be ignored in unify*)
let cons_map f = function
| Equality (t1,t2) -> Equality (f t1, f t2)
| TypeClass (t,c) -> TypeClass (t,c)

(* Since we mix typeclass constraints and type equality constraints during type checking,
   we pull out all the typeclass constraints to be dealt with later and then do the normal
   unification algo. [classes] is the set of class constraints that remain to be dealt with,
   and are written in terms of the original variables that came out of [simple_check']*)
let rec unify' classes = function
| [] -> (classes,[])
| (TypeClass (t1,c))::t -> unify' ((t1,c)::classes) t
| (Equality (t1,t2))::cons_tail ->
  if t1 = t2 then
  unify' classes cons_tail
  else match (t1,t2) with
  (* first we do the two symmetric variable cases; clunky due to way pattern matching works *)
  | (TypeVar v1, t2) ->
  (*t1 is a type variable, so if it is not free in t2, just replace t1 with t2 *)
  (if not (mem v1 (ftv t2)) then
  (* compute recursive part*)
  let rec_tail_unify' = unify' classes (map (cons_map (tsub t2 v1)) cons_tail) in
  (* compose with the map sending v1 -> t2*)
  (fst rec_tail_unify', sub_comp (snd rec_tail_unify') [(v1,t2)])
  else
  (* infinite type failure *)
  failwith (Printf.sprintf "Cannot solve type constraint %s = %s as this would require constructing an infinite type" (string_of_type t1) (string_of_type t2)))
  | (t1, TypeVar v2) ->
  (* symmetric case *)
  (if not (mem v2 (ftv t1)) then
  let rec_tail_unify' = unify' classes (map (cons_map (tsub t1 v2)) cons_tail) in
  (fst rec_tail_unify', sub_comp (snd rec_tail_unify') [(v2,t1)])
  else
  (* infinite type failure *)
  failwith (Printf.sprintf "Cannot solve type constraint %s = %s as this would require constructing an infinite type" (string_of_type t1) (string_of_type t2))
  )
  (* Neither of those cases held, so now we check if they are both function types *)
  | (Fun (t11,t12), Fun (t21,t22)) ->
    (* they are both functions *)
    unify' classes (Equality(t11,t21)::Equality(t12,t22)::cons_tail)
  (* Similarly, we check if they are both tuples *)
  | (Product tlist1, Product tlist2) -> 
    if length tlist1 <> length tlist2 then
    failwith (Printf.sprintf "Cannot solve type constraint %s = %s as these are products of unequal length" (string_of_type (Product tlist1)) (string_of_type (Product tlist2)))
    else 
    let new_cons = fold_left (fun acc (x,y) -> Equality(x,y)::acc) cons_tail (combine tlist1 tlist2) in
    unify' classes new_cons
  (* None of the special cases applied, so cannot be solved. *)
  | _ -> failwith (Printf.sprintf "Cannot solve type constraint %s = %s" (string_of_type t1) (string_of_type t2))

let unify = unify' []

let tcheck_simple_test_old e = let out = tcheck_simple'' [] e in
  (fst out, snd (unify (snd out)))

let print_sub_map =
  List.iter (fun x -> match x with (vname, etype) -> (Printf.printf "%s ↦ %s" (string_of_var vname) (string_of_type etype); print_newline ()))

(** [sub_vars sub_map t] gives back the type [t] but with type variables substituted as specificied in [sub_map] *)
let rec sub_vars sub_map t = 
  match t with
  | Fun (t1,t2) -> Fun (sub_vars sub_map t1, sub_vars sub_map t2)
  | TypeVar a ->
    (match assoc_opt a sub_map with
    | None -> t 
    | Some t' -> t')
  | _ -> t

(* [qauntify t classes] gives back a type scheme that includes all the class constraints for free variables in [t] given in [classes]*)
let quantify t classes = failwith "unimplemented"

(*TODO: how do we generalize this to more easily deal with arbitrary type classes *)
let weakest_class_constraint = function
  |(TypeVar v,Printable) -> [(v,[Printable])]
  |(t,Printable) -> if printable t then [] else failwith (Printf.sprintf "Cannot solve class constraint %s %s" (string_of_typeclass Printable) (string_of_type t))

let rec remove_dups = function
| (h::t) -> if mem h t then t else h::(remove_dups t)
| [] -> []

let combine_class_constraints constraints_w_repeats =
  let vars_w_constraints = remove_dups (map (fun x -> match x with (v,c) -> v) constraints_w_repeats) in
  (* for each of these variables, find all their constraints and put them together, removing any repeats *)
  map (fun x -> (x,remove_dups (fold_left (fun acc cons -> if fst cons = x then acc @ (snd cons) else acc) [] constraints_w_repeats))) vars_w_constraints

(* accepts a list of class constraints on types and then returns the weakest constraints on the free type variables to ensure that they are satisfied *)
let weakest_class_constraints class_constraints : known_classes =
  (* use weakest_class_constraint to determine all constraints on type variables *)
  let constraints_w_repeats = flatten (map weakest_class_constraint class_constraints) in
  (* find all the variables that have constraints *)
  combine_class_constraints constraints_w_repeats

let tcheck_simple_compact venv texpr fresh_tvar known_classes =
  (* The checker outputs a type together with constraints and the next available type variable *)
  let out = tcheck_simple' venv texpr ([],fresh_tvar) in 
  let t = fst out in
  let classes_required,sub_map = unify (fst (snd out)) in
  let next_tvar = snd (snd out) in
  let t_out = sub_vars sub_map t in
  (* update the variables in the class constraints we got out *)
  let class_constraints = map (fun x -> match x with (x,y) -> (sub_vars sub_map x,y)) classes_required in
  (* determine what constraints these put on the type variables *)
  let new_var_constraints = weakest_class_constraints class_constraints in
  (* add in the class constraints we already knew *)
  let all_var_constraints = combine_class_constraints (flatten [new_var_constraints;known_classes]) in
  (* to get all the foralls, add an empty constraint for all the non-constrained type variables *)
  let empty_class_constraints =
    let empty = map (fun x -> (x,[])) (ftv t_out) in
    filter (fun x -> not (mem (fst x) (map fst all_var_constraints))) empty
  in
  let all_class_constraints = all_var_constraints @ empty_class_constraints in
  (t_out, next_tvar, all_class_constraints)

let tcheck_simple_test texpr =
  match (tcheck_simple_compact [] texpr init_name []) with
  | (x,_,c) -> (x,c)

(*let clear_except_var v venv =
filter (fun x -> (fst x) = v) venv*)

(** [combine_maps] combines two association list-defined functions, assuming that they agree on the intersections of their domains *)
let combine_maps venv1 venv2 =
  let keys1 = map fst venv1 in
  let venv2' = filter (fun x -> not (mem (fst x) keys1)) venv2 in
  venv1 @ venv2'

(* draw_name also passed the constraints along, but many times we don't want this *)
let pull_name = function
  | Sub n -> (Sub n, Sub (n+1))
  | _ -> failwith "fresh name source corrupted"

(* this helper works with a different state monad because it must keep track of the current
   subsitutions as well as the fresh variable name*)
let rec gen_new_tvars' t known =
  let pull_sub_so_far = fun (n,sub) -> (sub,(n,sub)) in
  let pull_name = fun (name,sub) ->
    match name with
    | Sub n -> (name,(Sub (n+1),sub))
    | _ -> failwith "fresh name source corrupted"
  in
  match t with
  | Integer -> return' (Integer,[])
  | Boolean -> return' (Boolean,[])
  | UnitType -> return' (UnitType,[])
  | TypeVar a ->
    (match assoc_opt a known with
    | None -> failwith "cannot generate new type with new type constraints"
    | Some c ->
      (let^ sub_so_far = pull_sub_so_far in
      match assoc_opt a sub_so_far with
      | None -> let^ fresh = pull_name in return' (TypeVar fresh,[(fresh,c)])
      | Some a' -> return' (TypeVar a', [(a',c)])
      )
    )
  | Fun (t1,t2) ->
      let^ t1',k1' = gen_new_tvars' t1 known in
      let^ t2',k2' = gen_new_tvars' t2 known in
      return' (Fun(t1',t2'), combine_class_constraints (k1' @ k2'))
  | Product tlist ->
      let^ new_tlist,new_known = fold_right
      (fun t acc -> let^ t',k' = gen_new_tvars' t known in
      let^ acc' = acc in
      return'((t'::(fst acc')),combine_class_constraints(k'@(snd acc')))) tlist (return' ([],[])) in
      return' ((Product new_tlist),new_known)
  | SumType _ -> failwith "unimplemented" 
(** [gen_new_tvars t known] gives back [t',venv',known'],
    [t'] is an equivalent type with fresh type
    variables and [known'] is a class constraint object that defines the constraints
    for all the free variables of [t'] (but not necessarily all the variables that
    were constrained in [known])*)
let gen_new_tvars t known s =
  let result = gen_new_tvars' t known (s,[]) in
  (fst result, fst (snd result))

(* return e2, a venv', and known_classes'
   where each instance of v is changed to a new variable name,
   each of which has type equivalent to t, but with distinct type variables for each.
   Note that venv' does NOT contain have mappings for all the free variables in e2, it
   only has mappings for these newly created variables.
  *)
let rec instance_sub_simple v t known_classes e2 =
  let quick_sub = instance_sub_simple v t known_classes in
  match e2 with
  | TInt _ -> return' (e2,[],[])
  | TBool _ -> return' (e2,[],[])
  | TPlus (e1,e2) ->
  let^ e1',venv1,known1 = quick_sub e1 in
  let^ e2',venv2,known2 = quick_sub e2 in
  return' (TPlus (e1,e2),combine_maps venv1 venv2, combine_maps known1 known2)
  | TTimes (e1,e2) ->
  let^ e1',venv1,known1 = quick_sub e1 in
  let^ e2',venv2,known2 = quick_sub e2 in
  return' (TTimes (e1,e2),combine_maps venv1 venv2, combine_maps known1 known2)
  | TEq (e1,e2) ->
  let^ e1',venv1,known1 = quick_sub e1 in
  let^ e2',venv2,known2 = quick_sub e2 in
  return' (TEq (e1,e2),combine_maps venv1 venv2, combine_maps known1 known2)
  | TLambda (e,arg,targ) ->
    if arg = v then return' (e2,[],[]) else
    let^ e',venv',known' = quick_sub e in
    return' (TLambda(e',arg,targ),venv',known')
  | TVar v' ->
    if not (v = v') then return' (e2,[], [])
    else
      let^ fresh = pull_name in
      let^ t',known' = gen_new_tvars t known_classes in
      return' (TVar fresh, [(fresh,t')], known')
  | TApplication (e1,e2) ->
    let^ e1',venv1,known1 = quick_sub e1 in
    let^ e2',venv2,known2 = quick_sub e2 in
    return' (TApplication (e1',e2'),combine_maps venv1 venv2, combine_maps known1 known2)
  | TIf (e1,e2,e3) ->
    let^ e1',venv1,known1 = quick_sub e1 in
    let^ e2',venv2,known2 = quick_sub e2 in
    let^ e3',venv3,known3 = quick_sub e3 in
    return' (TIf (e1',e2',e3'),combine_maps (combine_maps venv1 venv2) venv3, combine_maps (combine_maps known1 known2) known3)
  | TUnit -> return' (e2,[],[])
  | TPrint e ->
    let^ e',venv1,known1 = quick_sub e in
    return' (TPrint e', venv1, known1)
  | TProd elist ->
      let^ elist',venv',known' = fold_right
      (fun e acc ->
      let^ e',venv',known' = quick_sub e in
      let^ e_acc,venv_acc,k_acc = acc in
      return'(e'::e_acc, combine_maps venv_acc venv', combine_maps k_acc known')) elist (return' ([],[],[])) in
      return' (TProd(elist'),venv',known')
  | TSum (c,e) ->
      let^ e',v',k' = quick_sub e in
      return' (TSum (c,e'),v',k')
  | TProj (e,n,l) ->
      let^ e',v',k' = quick_sub e in
      return' (TProj (e',n,l),v',k')
  | TMatch (e,cases) ->
      let^ e',v',k' = quick_sub e in
      let^ cases',venv',known' = fold_right
      (fun (c,e) acc ->
      let^ e',venv',known' = quick_sub e in
      let^ e_acc,venv_acc,k_acc = acc in
      return'((c,e')::e_acc, combine_maps venv_acc venv', combine_maps k_acc known')) cases (return' ([],[],[])) in
      return' (TMatch(e',cases'),combine_maps v' venv', combine_maps k' known')



(* same as instance_sub but works on sugar*)
let rec instance_sub v t known_classes e2  = 
  let quick_sub = instance_sub v t known_classes in
  match e2 with
  | TBase e ->
    let^ e',venv',known' = instance_sub_simple v t known_classes e in
    return' (TBase e', venv',known')
  | TLet (v',e1,e2) ->
    (let^ e1',venv1,known1 = quick_sub e1 in
    (* instances of v = v' in e2 should be bound to v' here *)
    if v' = v then return' (TLet (v', e1', e2),venv1,known1) else
      let^ e2',venv2,known2 = quick_sub e2 in
      return' (TLet (v',e1',e2'),combine_maps venv1 venv2, combine_maps known1 known2)
    )
  | TLetRec (v',tv',e1,e2) ->
    (* in the recursive case, instances of v' = v in either expression are bound to the v' defined here *)
    if v = v' then return' (TLetRec (v',tv',e1,e2),[],[]) else
    let^ e1',venv1,known1 = quick_sub e1 in
    let^ e2',venv2,known2 = quick_sub e2 in
    return' (TLetRec (v',tv',e1',e2'), combine_maps venv1 venv2, combine_maps known1 known2)

(** [tcheck'] implements prenex polymorphism and haskell-style type classes
    [venv] gives the current variable -> type mapping
    [texpr] is the typed expression to be type checked
    [known_classes] are the known type class constraints on type variables
    TODO: add the argument [utenv], the environment of user defined types, and set up typechecking for newsum
    the state monad is used to keep track of the next fresh type variable name available
    The output of the function is a pair [expr_type * var_name] giving the next fresh
    type variable name that is available and the type of the expression that you put in*)
let rec tcheck' (venv : (var_name * expr_type) list) (known_classes : (var_name * (type_class list)) list) : typed_sugar -> (class_constrained_expr_type,var_name) state = function
| TBase expr ->
    (fun name -> 
    (*just call tcheck_simple_compact in order to get the type *)
    match tcheck_simple_compact venv expr name known_classes with
    | (t,fresh_out,class_out) -> ((t,class_out),fresh_out)
    )
  | TLet (v,e1,e2) -> (
  (* get the class constraints and the type using tcheck' *)
    let^ t1,class_out1 = tcheck' venv known_classes e1 in
    (* do instance-based type substitution into e2 *)
    (* for using instance_sub we only care about the class constraints for free type variables
       of t1, so we compute these constraints first as v_local_class.*)
    let v_local_tvars = ftv t1 in
    let v_local_class = filter (fun x -> mem (fst x) v_local_tvars) class_out1 in
    let^ e2',v_local_venv,v_local_known = instance_sub v t1 v_local_class e2 in
    (* note that the type variables in the domains of these local maps are new, so don't
       appear in the original map, meaning we can blindly concatenate them without checking
       for repeats*)
    let new_venv = venv @ v_local_venv in
    let new_known = known_classes @ v_local_known in
    (* finally we can type check e2', the modified version of e2*)
    tcheck' new_venv new_known e2'
    )
| TLetRec (v,tv,e1,e2) ->( 
  (* type check e1 and get the constraints and the type *)
    let venv = (v,tv)::venv in
    let^ t1,class_out1 = tcheck' venv known_classes e1 in
    (* do instance-based type substitution into e2 *)
    (* for using instance_sub we only care about the class constraints for free type variables
       of t1, so we compute these constraints first as v_local_class.*)
    let v_local_tvars = ftv t1 in
    let v_local_class = filter (fun x -> mem (fst x) v_local_tvars) class_out1 in
    let^ e2',v_local_venv,v_local_known = instance_sub v t1 v_local_class e2 in
    (* note that the type variables in the domains of these local maps are new, so don't
       appear in the original map, meaning we can blindly concatenate them without checking
       for repeats*)
    let new_venv : (var_name * expr_type) list = venv @ v_local_venv in
    let new_known : (var_name * (type_class list)) list = known_classes @ v_local_known in
    (* finally we can type check e2', the modified version of e2*)
    tcheck' new_venv new_known e2'
    )

(* [tcheck t_expr] is replaced by tcheck' above.
   This function did type checking in the simply typed lambda calculus (no type variables or polymorphism)*)
   (*
let rec tcheck venv : typed_sugar -> (error_msg,expr_type) either = function
| TBase expr -> tcheck_simple venv expr
| TLet (v,e1,e2) ->
  let* tv = tcheck venv e1 in
  tcheck ((v,tv)::(remove_assoc v venv)) e2 
| TLetRec (v,tv,e1,e2) ->
    let venv' = (v,tv)::(remove_assoc v venv) in
    let* t1 = tcheck venv' e1 in
    if t1 <> tv then Left (declared_mismatch_error v tv t1)
    else
    tcheck venv' e2 
*)

let typecheck sugar_e =
  let mtype = fst (tcheck' [] [] sugar_e init_name) in (mtype, strip sugar_e)

