open Definitions
open List

let rec strip : typed_expr -> sugar = function
| TLet (v,tv,e1,e2) -> Let (v, strip e1, strip e2)
| TLetRec (v,tv,e1,e2) -> LetRec (v, strip e1, strip e2)
| TInt n -> SInt n
| TFloat n -> SFloat n
| TBool b -> SBool b
| TVar v -> SVar v
| TLambda (e1,v,tv) -> SLambda (strip e1, v)
| TApplication (e1,e2) -> SApplication (strip e1, strip e2)
| TIf (e1,e2,e3) -> SIf (strip e1, strip e2, strip e3)
| TUnit -> SUnit
| TPrint e -> SPrint (strip e)
| TSum (name,e) -> SSum(name,strip e)
| TProd elist -> SProd(map strip elist)
| TMatch (e,cases) -> SMatch (strip e, map (fun (c,e) -> (c,strip e)) cases)
| TProj (e,n,l) -> SProj (strip e, n)
| NewSum (name, targs, cons, cont) -> strip cont
| TNeg e -> SNeg (strip e)
| TBinop (e1,op,e2) -> SBinop (strip e1,op,strip e2)
(* NewSums are only for typechecking so we strip them out*)

(**[venv] is the type of the variable type environment.
   Ideally this would be a map but setting this up is giving me issues so I'm starting by using an association list.
   Invariant is that keys should not appear more than once (otherwise [remove_assoc] will not remove all bindings.*)
type venv = (var_name * expr_type) list
type utenv = (user_var_name * (user_var_name list) * ((user_var_name * expr_type) list)) list

let print_sub_map =
  List.iter (fun x -> match x with (vname, etype) -> (Printf.printf "%s ↦ %s" (string_of_var vname) (string_of_type etype); print_newline ()))
let print_var_sub_map =
  List.iter (fun x -> match x with (vname_in, vname_out) -> (Printf.printf "%s ↦ %s" (string_of_var vname_in) (string_of_var vname_out); print_newline ()))
let undeclared_error v =  Printf.sprintf "The variable %s is undeclared" (string_of_var v)
(*let inferred_mismatch e t reason found = Printf.sprintf "Expression %s was expected to have type %s because %s but its actual type is %s" (string_of_typed_expr e) (string_of_type t) reason (string_of_type found)
let declared_mismatch_error v declared got = Printf.sprintf "%s had declared type %s but was equated to an expression of type %s" (string_of_var v) (string_of_type declared) (string_of_type got)
*)
(* may want to use this error messages *)

(** [tconstraint] is used to describe a type equality or type class constraint *)
type tconstraint =
| Equality of expr_type * expr_type
| TypeClass of expr_type * type_class
type constraints = tconstraint list

(** [string_of_tconstraint] can be used to print a [tconstraint] *)
let string_of_tconstraint = function
| Equality (t1,t2) -> Printf.sprintf "%s = %s" (string_of_type t1) (string_of_type t2)
| TypeClass (t,c) -> Printf.sprintf "%s is of typeclass %s" (string_of_type t) (string_of_typeclass c)

let string_of_constraints =
fold_left (fun acc x -> acc ^ "\n" ^ (string_of_tconstraint x)) ""

(** [constrain] is used to equate two types when working in the [state] monad used by [tcheck'] *)
let constrain t1 t2 _ (constraints,name) = ((),((Equality (t1,t2))::constraints,name))
(** [class_constrain] is used to create a typeclass constraint when working in the [state] monad used by [tcheck'] *)
let class_constrain t1 c _ (constraints,name) = ((),((TypeClass (t1,c))::constraints,name))
(** [ignore] takes a function and creates a new function that is the same but ignores an additional first argument, useful when you just want the side-effect of the last monadic function *)
let ignore f = fun _ -> f

(** [draw_name] gives back the next free name and updates the state. This works in the [state] monad used in [tcheck'] *)
let draw_name : (var_name,constraints * var_name) state = function
  | (c,Sub n) -> (Sub n,(c,Sub (n+1)))
  | _ -> failwith "type variable source corrupted, unable to draw name"

(** [sub_vars sub_map t] gives back the type [t] but with type variables substituted as specificied in [sub_map] *)
let rec sub_vars sub_map t = 
  match t with
  | Fun (t1,t2) -> Fun (sub_vars sub_map t1, sub_vars sub_map t2)
  | TypeVar a ->
    (match assoc_opt a sub_map with
    | None -> t 
    | Some t' -> t')
  | Product tlist -> Product (fold_right (fun x acc -> (sub_vars sub_map x)::acc) tlist [])
  | SumType (tname,targs) -> SumType(tname,map (sub_vars sub_map) targs)
  | Integer -> Integer
  | Boolean -> Boolean
  | UnitType -> UnitType
  | Floating -> Floating

let update_sub sub1 sub2 = map (fun (x,y) -> (x,sub_vars sub2 y)) sub1

(**[sub_comp sub2 sub1] gives back the composite map sub2 \circ sub1.
  Precondition: The domains of sub1 and sub2 are disjoint*)
let sub_comp sub2 sub1 =
  let sub1_new = update_sub sub1 sub2 in
  sub2 @ sub1_new

(** used in [unify'] when have t1 = t2 to make sure both satisfy all typeclass constraints needed of both. it updates the class constraints to include the maximum of the constraints for both [t1] and [t2] for each*)
let eq_class_constraints t1 t2 classes =
  let new1_constraints = map (fun (x,y) -> (t1,y)) (filter (fun x -> fst x = t2) classes) in
  let new2_constraints = map (fun (x,y) -> (t2,y)) (filter (fun x -> fst x = t1) classes) in
  (classes @ new1_constraints) @ new2_constraints

let tsub_into_constraints t v cons_tail = map (fun (x,y) -> (tsub t v x,tsub t v y)) cons_tail
let tsub_into_classconstraints t v lst = map (fun (x,y) -> (tsub t v x,y)) lst 

(* Since we mix typeclass constraints and type equality constraints during type checking,
   we pull out all the typeclass constraints to be dealt with later and then do the normal
   unification algo. [classes] is the set of class constraints that remain to be dealt with,
   and are written in terms of the original variables that came out of [simple_check']*)
let rec unify' classes eqconstraints =
match eqconstraints with
| [] -> (classes,[])
| (t1,t2)::cons_tail ->
  let classes = eq_class_constraints t1 t2 classes in
  if t1 = t2 then
  unify' classes cons_tail
  else
  match (t1,t2) with
  (* first we do the two symmetric variable cases; clunky due to way pattern matching works *)
  | (TypeVar v, t) ->
  (*t1 is a type variable, so if it is not free in t, just replace t1 with t *)
  (if not (mem v (ftv t)) then
  (* compute recursive part*)
  let rec_tail_unify' = unify' (tsub_into_classconstraints t v classes) (tsub_into_constraints t v cons_tail) in
  (* compose with the map sending v -> t*)
  (fst rec_tail_unify', sub_comp (snd rec_tail_unify') [(v,t)])
  else
  (* infinite type failure *)
  failwith (Printf.sprintf "Cannot solve type constraint %s = %s as this would require constructing an infinite type" (string_of_type t1) (string_of_type t)))
  | (t, TypeVar v) ->
  (*t1 is a type variable, so if it is not free in t, just replace t1 with t *)
  (if not (mem v (ftv t)) then
  (* compute recursive part*)
  let rec_tail_unify' = unify' (tsub_into_classconstraints t v classes) (tsub_into_constraints t v cons_tail) in
  (* compose with the map sending v -> t*)
  (fst rec_tail_unify', sub_comp (snd rec_tail_unify') [(v,t)])
  else
  (* infinite type failure *)
  failwith (Printf.sprintf "Cannot solve type constraint %s = %s as this would require constructing an infinite type" (string_of_type t1) (string_of_type t)))
  (* Neither of those cases held, so now we check if they are both function types *)
  | (Fun (t11,t12), Fun (t21,t22)) ->
    (* they are both functions *)
    unify' classes ((t11,t21)::(t12,t22)::cons_tail)
  (* Similarly, we check if they are both tuples *)
  | (Product tlist1, Product tlist2) -> 
    if length tlist1 <> length tlist2 then
    failwith (Printf.sprintf "Cannot solve type constraint %s = %s as these are products of unequal length" (string_of_type (Product tlist1)) (string_of_type (Product tlist2)))
    else 
    let new_cons = fold_left (fun acc (x,y) -> (x,y)::acc) cons_tail (combine tlist1 tlist2) in
    unify' classes new_cons
  (* None of the special cases applied, so cannot be solved. *)
  | (SumType(tname1,targs1), SumType(tname2,targs2)) ->
    if tname1 <> tname2 then
    failwith (Printf.sprintf "Cannot solve type constraint %s = %s as they are different sumtypes." (string_of_type t1) (string_of_type t2)) else
    let new_constraints = combine targs1 targs2 in
    unify' classes (cons_tail@new_constraints)
  | _ -> failwith (Printf.sprintf "Cannot solve type constraint %s = %s" (string_of_type t1) (string_of_type t2))

let sep_constraints =
  fold_left (fun (classlist,eqlist) x ->
    match x with
    | Equality (x,y) -> (classlist,(x,y)::eqlist)
    | TypeClass (x,y) -> ((x,y)::classlist,eqlist)
    ) ([],[])

let unify constraints =
  let classconstraints,eqconstraints = sep_constraints constraints in
  unify' classconstraints eqconstraints

(** [combine_maps] combines two association list-defined functions, assuming that they agree on the intersections of their domains *)
let combine_maps venv1 venv2 =
  let keys1 = map fst venv1 in
  let venv2' = filter (fun x -> not (mem (fst x) keys1)) venv2 in
  venv1 @ venv2'

(* draw_name also passed the constraints along, but many times we don't want this *)
let pull_name = function
  | Sub n -> (Sub n, Sub (n+1))
  | _ -> failwith "fresh name source corrupted"


let weakest_class_constraint = function
  |(TypeVar v,c) -> [(v,[c])]
  |(t,Printable) -> if printable t then [] else failwith (Printf.sprintf "Cannot solve class constraint %s %s" (string_of_typeclass Printable) (string_of_type t))
  |(t,Equality) -> if has_equality t then [] else failwith (Printf.sprintf "Cannot solve class constraint %s %s" (string_of_typeclass Equality) (string_of_type t))
  |(Floating, Number) -> []
  |(Integer, Number) -> []
  |(t,Number) -> failwith (Printf.sprintf "Cannot solve class constraint %s %s" (string_of_typeclass Equality) (string_of_type t))
  |(t, Ordered) -> if has_order t then [] else failwith (Printf.sprintf "Cannot solve class constraint %s %s" (string_of_typeclass Equality) (string_of_type t))
  |(_,UserClass _) -> failwith "user type classes not implemented yet"

let rec remove_dups = function
| [] -> []
| h::t -> if mem h t then remove_dups t else h::(remove_dups t)

let combine_class_constraints constraints_w_repeats =
  let vars_w_constraints = remove_dups (map (fun x -> match x with (v,c) -> v) constraints_w_repeats) in
  (* for each of these variables, find all their constraints and put them together, removing any repeats *)
  map (fun x -> (x,remove_dups (fold_left (fun acc cons -> if fst cons = x then acc @ (filter (fun x -> not (mem x acc)) (snd cons)) else acc) [] constraints_w_repeats))) vars_w_constraints

(* accepts a list of class constraints on types and then returns the weakest constraints on the free type variables to ensure that they are satisfied *)
let weakest_class_constraints class_constraints : known_classes =
  (* use weakest_class_constraint to determine all constraints on type variables *)
  let constraints_w_repeats = flatten (map weakest_class_constraint class_constraints) in
  (* find all the variables that have constraints *)
  combine_class_constraints constraints_w_repeats
(* this helper works with a different state monad because it must keep track of the current
   subsitutions as well as the fresh variable name*)
let rec gen_new_tvars' t =
  let pull_sub_so_far = fun (n,sub,known) -> (sub,(n,sub,known)) in
  let add_to_known bind_list = fun (n,sub,known) -> ((),(n,sub,known @ bind_list)) in
  let pull_known = fun (n,sub,known) -> (known,(n,sub,known)) in
  let pull_name a = fun (name,sub,known) ->
    match name with
    | Sub n -> (name,(Sub (n+1),(a,name)::sub, known))
    | _ -> failwith "fresh name source corrupted"
  in
  match t with
  | Integer -> return Integer
  | Floating -> return Floating
  | Boolean -> return Boolean
  | UnitType -> return UnitType
  | TypeVar a ->
    let* known = pull_known in
    (match assoc_opt a known with
    | None -> failwith "Unbound type variable in expression; cannot complete substitution."
    | Some c ->
      (let* sub_so_far = pull_sub_so_far in
      match assoc_opt a sub_so_far with
      | None -> let* fresh = pull_name a in add_to_known [(fresh,c)] >>= ignore(return (TypeVar fresh))
      | Some a' -> return (TypeVar a')
      )
    )
  | Fun (t1,t2) ->
      let* t1' = gen_new_tvars' t1 in
      let* t2' = gen_new_tvars' t2 in
      return (Fun(t1',t2'))
  | Product tlist ->
      let* tlist' = state_fmap gen_new_tvars' tlist in
      return (Product tlist')
  | SumType (name,targs) ->
    let* targs' = state_fmap gen_new_tvars' targs in
    return(SumType(name, targs'))


(** [gen_new_tvars t known] gives back [t',known'],
    [t'] is an equivalent type with fresh type
    variables and [known'] is a class constraint object that defines the constraints
    for all the free variables of [t'] (but not necessarily all the variables that
    were constrained in [known])*)
let gen_new_tvars t known fresh_in =
  let result,(fresh_out,sub_map,new_known) = gen_new_tvars' t (fresh_in,[],known) in ((result,new_known),fresh_out)

(* same as gen_new_tvars but gives the substitution map used back as well *)
let gen_new_tvars_and_sub t known fresh_in : (class_constrained_expr_type * (var_name * var_name) list) * var_name =
  let result,(fresh_out,sub_map,new_known) = gen_new_tvars' t (fresh_in,[],known) in (((result,new_known),sub_map),fresh_out)

(* this binding is just the same as the gen_new_tvars_and_sub just above it but passes through constraints so that we can use it in
   tcheck' without having to exit the monad*)
let constrain_monad_gen_tvars_and_sub t known (constraints,fresh_in) = 
  let result,(fresh_out,sub_map,new_known) = gen_new_tvars' t (fresh_in,[],known) in (((result,new_known),sub_map),(constraints,fresh_out))

(* given binop gives back first arg type, second arg type, output type *)
let expected_type op =
match op with
| Mod -> (Integer,Integer,SumType("option",[Integer]))
| L -> (Integer,Integer,Boolean)
| G -> (Integer,Integer,Boolean)
| And -> (Boolean,Boolean,Boolean)
| Or -> (Boolean,Boolean,Boolean)
| _ -> failwith (Printf.sprintf "expected_type does not work on binop %s" (string_of_binop op))

let is_num_op op =
  match op with
  | Div -> true
  | Plus -> true
  | Times -> true
  | _ -> false

let is_ord_op op =
  match op with
  | L -> true
  | G -> true
  | _ -> false

let t_out_num_op op =
  match op with
  | Div -> None
  | Plus -> None 
  | Times -> None 
  | L -> Some Boolean
  | G -> Some Boolean 
  | _ -> failwith "the function t_out_num_op should only be called on number operations"


(* return e2, a venv', and known_classes'
   where each instance of v is changed to a new variable name,
   each of which has type equivalent to t, but with distinct type variables for each.
   Note that venv' does NOT contain have mappings for all the free variables in e2, it
   only has mappings for these newly created variables.
  *)
let rec instance_sub v t known_classes e2  = 
  let quick_sub = instance_sub v t known_classes in
  match e2 with
  | TLet (v',tv',e1,e2) ->
    (let* e1',venv1,known1 = quick_sub e1 in
    (* instances of v = v' in e2 should be bound to v' here *)
    if v' = v then return (TLet (v',tv', e1', e2),venv1,known1) else
      let* e2',venv2,known2 = quick_sub e2 in
      return (TLet (v',tv',e1',e2'),combine_maps venv1 venv2, combine_maps known1 known2)
    )
  | TLetRec (v',tv',e1,e2) ->
    (* in the recursive case, instances of v' = v in either expression are bound to the v' defined here *)
    if v = v' then return (TLetRec (v',tv',e1,e2),[],[]) else
    let* e1',venv1,known1 = quick_sub e1 in
    let* e2',venv2,known2 = quick_sub e2 in
    return (TLetRec (v',tv',e1',e2'), combine_maps venv1 venv2, combine_maps known1 known2)
  | TInt _ -> return (e2,[],[])
  | TFloat _ -> return (e2,[],[])
  | TBool _ -> return (e2,[],[])
  | TLambda (e,arg,targ) ->
    if arg = v then return (e2,[],[]) else
    let* e',venv',known' = quick_sub e in
    return (TLambda(e',arg,targ),venv',known')
  | TVar v' ->
    if not (v = v') then return (e2,[], [])
    else
      let* fresh = pull_name in
      let* t',known' = gen_new_tvars t known_classes in
      return (TVar fresh, [(fresh,t')], known')
  | TApplication (e1,e2) ->
    let* e1',venv1,known1 = quick_sub e1 in
    let* e2',venv2,known2 = quick_sub e2 in
    return (TApplication (e1',e2'),combine_maps venv1 venv2, combine_maps known1 known2)
  | TIf (e1,e2,e3) ->
    let* e1',venv1,known1 = quick_sub e1 in
    let* e2',venv2,known2 = quick_sub e2 in
    let* e3',venv3,known3 = quick_sub e3 in
    return (TIf (e1',e2',e3'),combine_maps (combine_maps venv1 venv2) venv3, combine_maps (combine_maps known1 known2) known3)
  | TUnit -> return (e2,[],[])
  | TPrint e ->
    let* e',venv1,known1 = quick_sub e in
    return (TPrint e', venv1, known1)
  | TProd elist ->
      let* elist',venv',known' = fold_right
      (fun e acc ->
      let* e',venv',known' = quick_sub e in
      let* e_acc,venv_acc,k_acc = acc in
      return(e'::e_acc, combine_maps venv_acc venv', combine_maps k_acc known')) elist (return ([],[],[])) in
      return (TProd(elist'),venv',known')
  | TSum (c,e) ->
      let* e',v',k' = quick_sub e in
      return (TSum (c,e'),v',k')
  | TProj (e,n,l) ->
      let* e',v',k' = quick_sub e in
      return (TProj (e',n,l),v',k')
  | TMatch (e,cases) ->
      let* e',v',k' = quick_sub e in
      let* cases',venv',known' = fold_right
      (fun (c,e) acc ->
      let* e',venv',known' = quick_sub e in
      let* e_acc,venv_acc,k_acc = acc in
      return((c,e')::e_acc, combine_maps venv_acc venv', combine_maps k_acc known')) cases (return ([],[],[])) in
      return (TMatch(e',cases'),combine_maps v' venv', combine_maps k' known')
  | NewSum (tname,targs,tdef,cont) ->
    let* cont',venv',known' = quick_sub cont in
    return (NewSum(tname,targs,tdef,cont'),venv',known') 
  | TBinop (e1,op,e2) ->
    let* e1',v1,k1 = quick_sub e1 in
    let* e2',v2,k2 = quick_sub e2 in
    return (TBinop(e1',op,e2'), combine_maps v1 v2, combine_maps k1 k2)
  | TNeg e ->
    let* e',v',k' = quick_sub e in
    return (TNeg e',v',k')

(* gives all type names *)
let user_types utenv = map (fun (x,_,_) -> x) utenv
(* gives all constructor names *)
let user_cons (utenv:utenv) = concat (map (fun (_,_,z) -> map fst z) utenv)
(* gives mapping from constructor names to type names *)
let type_of_cons (utenv:utenv) =
  concat(map (fun (tname,_,cons_list) -> map (fun cons_name -> (fst cons_name,tname)) cons_list) utenv)
let cons_for_t tname utenv =
  match find_opt (fun (x,_,_) -> x = tname) utenv with Some(_,_,cons_list) -> cons_list | None -> failwith ("could not find constructors for type " ^ tname)
let user_targs tname utenv =
  match find_opt (fun (x,_,_) -> x = tname) utenv with Some (_,targs,_) -> targs | None -> failwith ("could not find user targs for name " ^ tname) 
let num_targs tname utenv =
  let _,targs,_ = find (fun (x,_,_) -> x = tname) utenv in
  length targs

(* list of x repeated n times; infinite loop if n < 0 *)
let rec repeat n x =
  if n < 0 then failwith "cannot call repeat with negative arg" else
  if n = 0 then [] else x::(repeat (n-1) x)

let constrain_all equality_list =
  fold_left (fun acc (x,y) -> acc >>= constrain x y) (return ()) equality_list

let rec has_dups = function
| [] -> false
| h::t -> if mem h t then true else has_dups t


(* [tcheck'] returns a list of type equality and class constraints for the expression, together with the type of the expression *)
let rec tcheck' venv known_classes (utenv:utenv) e : (expr_type,constraints * var_name) state = 
  (*Printf.printf "checking expression %s \n" (string_of_typed_expr e);*)
  match e with
| TInt _ -> return Integer
| TFloat _ -> return Floating
| TBool _ -> return Boolean
| TVar v -> (match assoc_opt v venv with
             | Some t -> return t
	     | None -> failwith (undeclared_error v))
| TBinop (e1,op,e2) -> (
  let* t1 = tcheck' venv known_classes utenv e1 in
  let* t2 = tcheck' venv known_classes utenv e2 in
  match op with
  | Eq ->
      let* _ = class_constrain t1 Equality () >>= class_constrain t2 Equality in
      let* _ = constrain t1 t2 () in
      return Boolean
  | _ ->
    if is_ord_op op then
      let* _ = class_constrain t1 Ordered () >>= class_constrain t2 Ordered in
      let* _ = constrain t1 t2 () in
      return Boolean
    else
    if is_num_op op then
      let* _ = class_constrain t1 Number () >>= class_constrain t2 Number in
      let* _ = constrain t1 t2 () in
      if op = Div then
        return (SumType ("Some", [t1]))
      else
        match t_out_num_op op with
        | Some t -> return t
        | None -> return t1
    else
      let expected1, expected2, out = expected_type op in
      constrain t1 expected1 () >>=
      constrain t2 expected2    >>=
      ignore(return out)
)
| TNeg e -> 
  let* t = tcheck' venv known_classes utenv e in
  constrain t Integer () >>=
  ignore(return Integer)
| TLambda (e,v,tv) ->
  let venv' = (v,tv)::venv in
  let* tbody = tcheck' venv' known_classes utenv e in
  return (Fun(tv,tbody))
| TApplication (e1,e2) ->
  (* bug with typeclasses seems to arise here: need to express that if t1 has typeclass constraints on its argument then t2 must meet these type class constraints *)
  let* t1 = tcheck' venv known_classes utenv e1 in
  let* t2 = tcheck' venv known_classes utenv e2 in
  let* new_name = draw_name in
  constrain t1 (Fun(t2,TypeVar new_name)) ()
  >>= ignore(return (TypeVar new_name))
| TIf (e1,e2,e3) ->
  let* t1 = tcheck' venv known_classes utenv e1 in
  let* t2 = tcheck' venv known_classes utenv e2 in
  let* t3 = tcheck' venv known_classes utenv e3 in
  constrain t1 Boolean () >>= constrain t2 t3 >>= ignore (return t2)
| TUnit -> return UnitType
| TPrint e ->
  let* t = tcheck' venv known_classes utenv e in
  class_constrain t Printable () >>= ignore(return UnitType)
| TSum (cons,e) ->(
  match assoc_opt cons (type_of_cons utenv) with
  | None -> failwith (Printf.sprintf "the constructor %s is not defined" cons)
  | Some tname ->
    (* use the type name to look up the type definition *)
    let _,targs,constructors = find (fun (x,_,_) -> x = tname) utenv in
    (* in the following we want to think of targs as types, not user_var_names = strings *)
    let targs = map (fun x -> Name x) targs in
    (* look up the type that the constructor cons expects *)
    let expected_type = snd (find (fun x -> fst x = cons) constructors) in
    let* t = tcheck' venv known_classes utenv e in
    (* generate fresh type variables for the expected type. The type variable names in the
       definition of the type may conflict with names in the current name space *)
    let* (expected_type,_),sub_map = constrain_monad_gen_tvars_and_sub expected_type (map (fun x -> (x,[])) targs) in
    (* important that sub_map is a total function on targs *)
    let sub_map = map (fun x -> match assoc_opt x sub_map with Some v -> (x,v) | None -> (x,x)) targs in
    (* Then we add constraints to ensure that e has the correct type *)
    let* _ = constrain expected_type t () in
    (* Next we compute the new type arguments *)
    let targs_here = map (fun x -> TypeVar(assoc x sub_map)) targs in
    return (SumType(tname,targs_here))
    )
| TProd elist ->
  let* tlist = fold_right (fun x acc -> let* t_new = tcheck' venv known_classes utenv x in let* acc' = acc in return (t_new::acc')) elist (return []) in
  return (Product tlist)
| TMatch (e,cases) ->
  (* check the type of e *)
  let* t = tcheck' venv known_classes utenv e in
  (* look at first case, find type, constrain t to be that type *)
  (match cases with
  | [] -> failwith "cannot have match statement with no cases"
  | (first_case_name,_)::_ -> (
    match assoc_opt first_case_name (type_of_cons utenv) with
    | None -> failwith (Printf.sprintf "Constructor %s does not exist" first_case_name)
    | Some tname ->
  (* generate fresh targs for the potential type of e *)
  let* targs = state_fmap (fun _ -> draw_name) (repeat (num_targs tname utenv) ()) in
  let targs = map (fun x -> TypeVar x) targs in
  constrain t (SumType(tname, targs)) () >>=
  fun _ ->
  let sub_map = combine (map (fun x -> Name x) (user_targs tname utenv)) targs in 
  (* get back the constructors and types, substituting in the targs we have*)
  let cons = map (fun (cons_name,cons_t) -> (cons_name,sub_vars sub_map cons_t)) (cons_for_t tname utenv) in 
  (* verify that the matches in each of the cases correspond to one of these constructors*)
  let cases_matched = map fst cases in
  let cons_cases = map fst cons in
  let difference lst1 lst2 = filter (fun x -> not (mem x lst2)) lst1 in
  let non_existent_cases = difference cases_matched cons_cases in
  if not ([] = non_existent_cases) then
  failwith (fold_left (fun acc x -> x ^ acc) "" (map (Printf.sprintf "the case %s does not have a corresponding constructor. ") non_existent_cases)) else
  (* check that every constructor has a case, print warnings if not *)
  let missing_cases = difference cons_cases cases_matched in
  List.iter (Printf.printf "Warning: missing case %s.\n") missing_cases;
  (* for each case, check that the type expected by the constructor is the same as the type that the function expects as an argument *)
    let expected_tlist = map (fun (case,_) -> assoc case cons) cases in
  (* tclass constraints should be getting put in here... *)
    let* case_funtypes = state_fmap (fun (case_name,foo) -> let* result = tcheck' venv known_classes utenv foo in return(case_name,result)) cases in
    let* in_out = state_fmap (fun (case_name,case_t) -> 
     let* t1 = draw_name in
     let* t2 = draw_name in
     constrain case_t (Fun(TypeVar(t1),TypeVar(t2))) () >>=
     ignore(return(TypeVar(t1),TypeVar(t2)))
      ) case_funtypes in 
    let* _ = constrain_all (combine expected_tlist (map fst in_out)) in
  (* check that the output of every case is the same type, and return that type *)
    match in_out with
    | [] -> failwith "no matches in match statement"
    | case1::cases_tail ->
      let fst_out_t = snd (hd in_out) in
      let* _ = constrain_all (map (fun case_out_t -> (fst_out_t,case_out_t)) (tl (map snd in_out))) in
      return fst_out_t
  )
  )
| TProj (e,n,l) ->
  (* note we zero index *)
  if n >= l || n < 0 then failwith "index out of bounds" else
  if l < 0 then failwith "tuples of negative length are not allowed" else
  (* generate a generic type for product of length l and constrain e to have this type *)
  let rec make_gen_prod' so_far_done tlist_so_far l =
    if so_far_done = l then return tlist_so_far else
    let* t_new = draw_name in make_gen_prod' (so_far_done + 1) ((TypeVar t_new)::tlist_so_far) l
    in
  let make_gen_prod l = let* tlist = make_gen_prod' 0 [] l in return ((Product tlist),nth tlist n) in
  let* gen_prod,t_out = make_gen_prod l in
  let* te = tcheck' venv known_classes utenv e in
  constrain te gen_prod () >>= ignore(return t_out)
| TLet (v,tv,e1,e2) ->
    (fun (constraints,fresh) ->
    (* application_trick just applies the identity function of the user-annotated type to the result, forcing the variable to have the annotated type *)
    let application_trick = (TApplication((TLambda(TVar(Name "x"), Name "x", tv), e1))) in
    let t1,fresh,var_constraints,sub_map = tcheck_compact venv application_trick fresh known_classes utenv in
    (* important to do this so that type inference from this let expression will also effect later occurrences of the same type *)
    let venv = (v,t1)::venv in
    (* do instance-based type substitution into e2 *)
    (* for using instance_sub we only care about the class constraints for free type variables of t1, so we compute these constraints first as v_local_class.*)
    (*let v_local_tvars = ftv t1 in
    let v_local_class = filter (fun x -> mem (fst x) v_local_tvars) var_constraints in*)
    let (e2',v_local_venv,v_local_known),fresh = instance_sub v t1 var_constraints e2 fresh in
    (* note that the type variables in the domains of these local maps are new, so don't
       appear in the original map, meaning we can blindly concatenate them without checking
       for repeats*)
    let new_venv : (var_name * expr_type) list = venv @ v_local_venv in
    let new_known : (var_name * (type_class list)) list = known_classes @ v_local_known in
    let expand lst = concat (map (fun (x,lsty) -> map (fun y -> (x,y)) lsty) lst) in
    let constraints = remove_dups(constraints@(map (fun (tvar,tclass) -> TypeClass(TypeVar(tvar),tclass)) (expand new_known))) in
    let constraints = remove_dups(constraints@(map (fun (v,t) -> Equality(TypeVar(v),t)) sub_map)) in
    (* now we can finally check our new e2' --- we did not increase the number of constraints
       because tcheck_compact will have called unify to eliminate all the new constraints created in e1,
       leaving only the new type class constraints that go into new_known*)
    tcheck' new_venv new_known utenv e2' (constraints,fresh))
| TLetRec (v,tv,e1,e2) ->
    let venv = (v,tv)::venv in
    tcheck' venv known_classes utenv (TLet(v,tv,e1,e2))
    (*
    (fun (constraints,fresh) ->
    let venv = (v,tv)::venv in
    let application_trick = (TApplication((TLambda(TVar(Name "x"), Name "x", tv), e1))) in
    let t1,fresh,var_constraints = tcheck_compact venv application_trick fresh known_classes utenv in
    (* do instance-based type substitution into e2 *)
    (* for using instance_sub we only care about the class constraints for free type variables
       of t1, so we compute these constraints first as v_local_class.*)
    let v_local_tvars = ftv t1 in
    let v_local_class = filter (fun x -> mem (fst x) v_local_tvars) var_constraints in
    let (e2',v_local_venv,v_local_known),fresh = instance_sub v t1 v_local_class e2 fresh in
    (* note that the type variables in the domains of these local maps are new, so don't
       appear in the original map, meaning we can blindly concatenate them without checking
       for repeats*)
    let new_venv : (var_name * expr_type) list = venv @ v_local_venv in
    let new_known : (var_name * (type_class list)) list = known_classes @ v_local_known in
    let expand lst = concat (map (fun (x,lsty) -> map (fun y -> (x,y)) lsty) lst) in
    let constraints = remove_dups(constraints@(map (fun (tvar,tclass) -> TypeClass(TypeVar(tvar),tclass)) (expand new_known))) in
    (* now we can finally check our new e2' --- we did not increase the number of constraints
       because tcheck_compact will have called unify to eliminate all the new constraints created in e1,
       leaving only the new type class constraints that go into new_known*)
    tcheck' new_venv new_known utenv e2' (constraints,fresh))
    *)
| NewSum (name,targs,cons,cont) ->
    (* check that this type name hasn't already been used *)
    if mem name (user_types utenv) then failwith (Printf.sprintf "type name %s already taken" name) else
    (* check that none of these constructors have already been used *)
    if not (for_all (fun x -> not (mem x (user_cons utenv))) (map fst cons)) then failwith (Printf.sprintf "some constructor in declaration of type %s already used" name) else
    if has_dups targs then failwith (Printf.sprintf "error in definition of type %s, duplicate type variables" name) else
    (* add to the user type environment *)
    let utenv = (name,targs,cons)::utenv in
    tcheck' venv known_classes utenv cont

(* [tcheck_compact] uses [tcheck'] and [unify] to determine an expressions constraints, solve them, and return a type, the next fresh variable, and the class constraints *)
and tcheck_compact venv texpr fresh_tvar known_classes utenv =
  (* The checker outputs a type together with constraints and the next available type variable *)
  let out = tcheck' venv known_classes utenv texpr ([],fresh_tvar) in 
  let t = fst out in
  let classes_required,sub_map = unify (fst (snd out)) in
  let next_tvar = snd (snd out) in
  let t_out = sub_vars sub_map t in
  (* update the variables in the class constraints we got out *)
  let class_constraints = remove_dups classes_required in
  (* determine what constraints these put on the type variables *)
  let new_var_constraints = weakest_class_constraints class_constraints in
  (* add in the class constraints we already knew *)
  (*let all_var_constraints = remove_dups (combine_class_constraints (flatten [new_var_constraints;known_classes])) in*)
  (* to get all the foralls, add an empty constraint for all the non-constrained type variables *)
  let empty_class_constraints =
    let constrained_vars = map fst new_var_constraints in
    let unconstrained_vars = filter (fun x -> not (mem x constrained_vars)) (ftv t_out) in
    map (fun x -> (x,[])) unconstrained_vars
  in
  let all_class_constraints = new_var_constraints @ empty_class_constraints in
  (*print_endline "all var constrained variables";
  List.iter print_endline ((map (fun (x,y) -> string_of_var x)) all_class_constraints); *)
  (t_out, next_tvar, all_class_constraints, sub_map)

(** [tcheck] implements prenex polymorphism and haskell-style type classes
    [name] is the next name available for type variables
    returns a class constrained type and the next fresh variable*)
let tcheck expr name : class_constrained_expr_type * var_name =
    (*just call tcheck_compact in order to get the type *)
    match tcheck_compact [] expr name [] [] with
    | (t,fresh_out,class_out,_) -> ((t,class_out),fresh_out)


let add_type expr = function
  | (name,targs, tdef) ->
  return(NewSum(name,targs,tdef,expr))

let add_def expr = function
  | (recursive,name,odef) ->
    let* tvar = pull_name in
    let* def = annotate_opt_t_expr odef in
    return(if recursive then TLetRec(name,TypeVar(tvar),def,expr) else TLet(name,TypeVar(tvar),def,expr))

type ('a,'b) either = Left of 'a | Right of 'b

let rec add_all_of expr = function
  | (Left x)::t -> let* rest = add_all_of expr t in add_def rest x
  | (Right x)::t -> let* rest = add_all_of expr t in add_type rest x
  | [] -> return expr

let oexpr_from_string s =
  let lexbuf = Lexing.from_string s in
  Parser.prog Lexer.token lexbuf

let list_def = Right ("list", ["'a"], [("Nil",UnitType);("Cons", Product [TypeVar(Name"'a");SumType("list",[TypeVar(Name"'a")])])])

let option_def = Right ("option",["'a"],[("None",UnitType);("Some",TypeVar(Name("'a")))])

let print_def = Left (false, Name "print",OLambda(OPrint(OVar(Name"x")),Name"x",None))

let map_body = oexpr_from_string
"lambda f . lambda lst .
match lst with
  | Nil x -> Nil
  | Cons pair ->
    Cons(f (proj 2 0 pair), map f (proj 2 1 pair))"

let map_def = Left (true, Name "map", map_body)

let base_defs = [list_def;option_def;print_def;map_def]

let put_in_base_defs expr fresh = add_all_of expr base_defs fresh

let typecheck expr init_name =
  let (expr',fresh) = put_in_base_defs expr init_name in
  let (mtype,fresh) = tcheck expr' fresh in
  (mtype, strip expr', fresh)
