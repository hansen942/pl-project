open Definitions
open List

(* path of file we are typechecking *)
let file = ref ""

type explanation = string

let debug = ref false

(* SOME GENERAL FUNCTIONS *)
(* returns list where the n^{th} element is the pair (x,y) where x and y are the n^{th} elements of the lists
   throws an error if the lists are of unequal length*)
let rec zip lst1 lst2 =
  match lst1, lst2 with
  | h1::t1, h2::t2 -> (h1,h2)::(zip t1 t2)
  | [], [] -> []
  | _, _ -> failwith "cannot call zip on lists of unequal length"

let rec has_dups = function
  | [] -> false
  | h::t -> if mem h t then true else has_dups t

(* DEFINE THE STATE OF THE TYPECHECKER AND SOME ASSOCIATED HELPERS *)
type state = {
  type_equalities : ((expr_type * expr_type * loc_info * explanation) list) ref;
  known_classes : (var_name * (type_class list)) list ref;
  required_classes : (expr_type * type_class * loc_info * explanation) list ref;
  (* variable_types acts like a stack, so when a variable goes out of scope it should be popped *)
  variable_types : (var_name * (expr_type * loc_info * explanation)) list ref;
  (* TODO: change tcheck so that it uses depth_var_stack to throw away variables when they go out of scope *)
  depth_var_stack : int ref;
  fresh_var : var_name ref;
  user_types : (user_var_name * user_var_name list * (user_var_name * expr_type) list * loc_info) list ref;
  (* needed to keep track of substitutions globally *)
  sub_so_far : (var_name * expr_type) list ref;
  tracking : expr_type ref
}

let init_state fresh = ref {
  type_equalities = ref [];
  known_classes = ref [];
  required_classes = ref[];
  variable_types = ref [];
  depth_var_stack = ref 0;
  fresh_var = fresh;
  user_types = ref [
    ("option", ["'a"], [("Some", TypeVar((Name "'a"))); ("None", UnitType)], Lexing.dummy_pos);
    ("list", ["'a"], [("Cons", Product[TypeVar((Name "'a"));SumType("list",[TypeVar(Name "'a")])]); ("Nil", UnitType)], Lexing.dummy_pos)
  ];
  sub_so_far = ref [];
  tracking = ref UnitType
}

(* get a fresh variable *)
let get_fresh state =
  let result = !((!state).fresh_var) in
  (!state).fresh_var := (match result with Sub n -> Sub (n + 1) | Name _ -> failwith "state corrupted");
  result

(* HELPERS FOR USER TYPE ENVIRONMENT *)

(* list of all constructors *)
let cons_list state =
  fold_left (fun acc (_,_,def_list,_) -> acc@(map fst def_list)) [] !(!state.user_types)

(* is name a constructor *)
let is_cons state name =
  mem name (cons_list state)

(* gives the entry in the user_types list
   associated with the constructor name
   Raises exception if name is not a constructor*)
let entry_of_cons state name =
  find (fun (_,_,def_list,_) -> mem name (map fst def_list)) !(!state.user_types)

let add_type state name type_args def_list loc =
  !state.user_types := (name,type_args,def_list,loc)::!(!state.user_types)

let user_types state = map (fun (name,_,_,_) -> name) !(!state.user_types)

let is_type state name = mem name (user_types state)

let entry_of_type state name = find (fun (u,_,_,_) -> u = name) !(!state.user_types)

(* HELPERS FOR ADDING AND LOOKING UP CONSTRAINTS*)

let apply_sub_so_far state t =
  fold_left (fun acc (x,t') -> tsub t' x acc) t !(!state.sub_so_far)

(* add the constraints t1 = t2, saying it was inferred at location loc and the reason it is necessary is described in msg *)
let add_type_equality state t1 t2 loc msg =
  (!state.type_equalities) := (t1,t2,loc,msg) :: !(!state.type_equalities)
  
(* add the constraints t1 = t2, saying it was inferred at location loc and the reason it is necessary is described in msg *)
let add_type_class_required state t c loc msg =
  (!state.required_classes) := (t,c,loc,msg) :: !(!state.required_classes)

(* if we know that x (a type variable name) must be of typeclass c, then call this function to store this in state *)
let add_known state x c =
  let rec find_curr_classes lst x =
    match lst with
    | [] -> (None, [])
    | (x',c')::t -> if x' = x then (Some c', t) else let h = (x',c') in match (find_curr_classes t x) with (result,t') -> (result,h::t')
  in
    match find_curr_classes !((!state).known_classes) x with
    | (Some already_known, l) -> if List.mem c already_known then ()
                                 else (!state).known_classes := (x,c::already_known)::l
    | (None,l) -> (!state).known_classes := (x,[c])::l

(* use to test if we know that x is of typeclass c *)
let is_known state x c =
  (!state).known_classes := (x,c) :: !((!state).known_classes)

(* use to return all known typeclasses that x must satisfy *)
let type_classes_of state x =
  match assoc_opt x !(!state.known_classes) with
  | None -> []
  | Some lst -> lst

(* HELPERS FOR VARIABLE TYPE STACK *)

(* used to push the binding (v_name,t_of_v) onto the variable environment stack with message msg and inf location l *)
let push_var_type state v_name t_of_v l msg =
  !state.variable_types := (v_name, (t_of_v, l, msg)) :: !(!state.variable_types);
  !state.depth_var_stack := !(!state.depth_var_stack) + 1

(* used to remove most recent variable binding *)
let pop_var_binding state =
  !state.variable_types := tl !(!state.variable_types);
  !state.depth_var_stack := !(!state.depth_var_stack) - 1

(* lookup the type of the variable x in the variable environment in state *)
let lookup state x =
  let venv = !((!state).variable_types) in
  assoc_opt x venv


(* DEFINE A BUNCH OF STUFF TO PRINT OUT THE STATE OF THE TYPECHECKER *)
(* change to false to avoid printouts *)

let display filename location =
  let file = open_in filename in
  let lexbuf = Lexing.from_channel file in
  Visualizer.print_out location lexbuf

let display_failure location msg =
  let file = open_in !file in
  let lexbuf = Lexing.from_channel file in
  Visualizer.print_out location lexbuf;
  print_newline ();
  print_endline msg;
  failwith "type error"

let string_of_loc : Lexing.position -> string = function
  | {pos_lnum = line; pos_bol = bol; pos_cnum = cnum} -> Printf.sprintf "line %s, position %s" (string_of_int line) (string_of_int (cnum - bol))

let string_of_type_equalities type_equalities =
  fold_left (fun acc (x,y,l,msg) -> acc^Printf.sprintf "%s = %s inferred at %s because %s\n" (string_of_type x) (string_of_type y) (string_of_loc l) msg) "" !type_equalities

let string_of_required_classes required_classes =
  fold_left (fun acc (x,y,l,msg) -> acc^Printf.sprintf "%s %s inferred at %s because %s\n" (string_of_typeclass y) (string_of_type x) (string_of_loc l) msg) "" !required_classes

let string_of_known_classes class_constraints =
  let string_of_multi_classes classes =
    match classes with
    | [] -> failwith "should not call string_of_known_classes on unconstrainted variable"
    | [c] -> string_of_typeclass c
    | h::t -> Printf.sprintf "(%s)" (fold_left (fun acc x -> acc^", "^(string_of_typeclass x)) (string_of_typeclass h) t)
  in
  fold_left (fun acc (x,y) -> acc^Printf.sprintf "%s %s\n" (string_of_multi_classes y) (string_of_var x)) "" !class_constraints

let string_of_venv venv =
  fold_left (fun acc (x,(y,l,msg)) -> acc^Printf.sprintf "%s : %s inferred at %s because %s\n" (string_of_var x) (string_of_type y) (string_of_loc l) msg) "" !venv

let string_of_sub sub_so_far =
  fold_left (fun acc (x,t) -> acc^Printf.sprintf "%s = %s\n" (string_of_var x) (string_of_type t)) "" !sub_so_far

let string_of_state state =
  let string_equalities = string_of_type_equalities state.type_equalities in
  let string_known = string_of_known_classes state.known_classes in
  let string_required = string_of_required_classes state.required_classes in
  let string_venv = string_of_venv state.variable_types in
  let string_fresh = string_of_var !(state.fresh_var) in
  let string_sub = string_of_sub state.sub_so_far in
  let divider = (String.make 80 '=') in
  Printf.sprintf "Constraint Generation\n%s\n%s%s%s%s\nVariable Environment\n%s%s\nKnown Type Mapping\n%s\n%s\nNext Fresh Variable: %s\n" divider string_equalities string_known string_required divider string_venv divider string_sub divider string_fresh

let reset_display = fun _ -> 
  print_string "\x1b[2J\x1b[H";
  flush stdout

let wait _ = let _ = input_char stdin in ()

let display_state state loc msg =
  if !debug then(
  reset_display ();
  print_string (string_of_state !state);
  display (!file) loc;
  print_newline ();
  print_endline msg;
  flush stdout;
  wait ()
  )

(* DEFINE STUFF FOR PRINTING THE CONSTRAINTS AND STATE OF UNIFICATION *)


let display_constraints state msg =
  if !debug then (
  reset_display ();
  let string_equalities = string_of_type_equalities (!state).type_equalities in
  let string_known = string_of_known_classes (!state).known_classes in
  let string_required = string_of_required_classes (!state).required_classes in
  let string_fresh = string_of_var !((!state).fresh_var) in
  let sub_string = string_of_sub (!state).sub_so_far in
  let divider = (String.make 80 '=') in
  Printf.printf "Unification\n%s\nType Equalities\n%s%s\nTypeclass Constraints\n%sKnown Typeclasses\n%s\n%s\nKnown Mapping\n%s\n%s\nNext Fresh Variable: %s\n" divider string_equalities divider string_required string_known divider sub_string divider string_fresh;
  print_string msg;
  flush stdout;
  wait ()
  )

(* UNIFICATION *)

let rec add_weakest_var_classes state : expr_type * type_class -> unit = function
  | (TypeVar(v), c) -> add_known state v c
  | (t,Printable) -> if printable t then () else failwith (Printf.sprintf "cannot infer printable %s" (string_of_type t))
  | (Integer,Ordered) -> () 
  | (t,Ordered) -> failwith (Printf.sprintf "%s is not in the ord typeclass" (string_of_type t))
  | (t,Equality) ->(
      match t with
      | Fun(_,_) -> failwith (Printf.sprintf "%s is not in the eq typeclass" (string_of_type t))
      | SumType(_,_) -> failwith (Printf.sprintf "%s is not in the eq typeclass" (string_of_type t))
      | Product tlist -> let _ = map (fun x -> add_weakest_var_classes state (x,Equality)) tlist in ()
      | _ -> ()
    )
  | (Integer,Number) -> ()
  | (Floating,Number) -> ()
  | (t,Number) -> failwith (Printf.sprintf "%s is not in the num typeclass" (string_of_type t))

let rec reduce_typeclass_constraints state =
  match !((!state).required_classes) with
  | [] -> ()
  | (t,c,l,m)::tail ->
      display_constraints state (Printf.sprintf "dealing with the constraint %s %s that was inferred at %s because %s" (string_of_typeclass c) (string_of_type t) (string_of_loc l) m);
      add_weakest_var_classes state (t,c);
      (!state).required_classes := tail;
      reduce_typeclass_constraints state

let apply_sub sub state = 
  match sub with (x,t) ->
  (* apply to the type we're tracking *)
  !state.tracking := tsub t x !(!state.tracking);
  (* first apply the sub to all the elements of the type equality constraints*)
  display_constraints state (Printf.sprintf "applying substitution %s = %s" (string_of_var x) (string_of_type t));
  (!state).type_equalities := map (fun (t1,t2,l,m) -> (tsub t x t1, tsub t x t2,l,m)) !((!state).type_equalities);
  (* if we have a class cosntraint on x then add the required class constraint to t *)
  (match assoc_opt x !((!state).known_classes) with
  | Some c -> let new_required = map (fun c -> (t,c,Lexing.dummy_pos,"we did a substitution")) c in (!state).required_classes := !((!state).required_classes) @ new_required
  | None -> ());
  (* update sub_so_far *)
  (!state).sub_so_far := (x,t)::(map (fun(v,tv) -> (v, tsub t x tv)) !((!state).sub_so_far))



let rec unify state : unit =
  let drop_equality _ = (!state).type_equalities := tl !((!state).type_equalities) in
  match !((!state).type_equalities) with
  | [] -> ()
  | h::_->(
      match h with
      | (TypeVar t, t',l,m) ->
          display_constraints state (Printf.sprintf "dealing with the constraints %s = %s that was inferred at %s because %s" (string_of_var t) (string_of_type t') (string_of_loc l) m);
          drop_equality ();
          if (not (List.mem t (ftv t'))) then (apply_sub (t,t') state; reduce_typeclass_constraints state; unify state)
          else if TypeVar t <> t' then failwith (Printf.sprintf "cannot construct infinite type arising from constraint %s = %s" (string_of_var t) (string_of_type t')) else
          unify state 
          (*else failwith (Printf.sprintf "cannot construct infinite type arising from constraint %s = %s" (string_of_var t) (string_of_type t'))*)
      | (t', TypeVar t,l,m) ->(
          display_constraints state (Printf.sprintf "dealing with the constraint %s = %s that was inferred at %s because %s" (string_of_var t) (string_of_type t') (string_of_loc l) m);
          drop_equality ();
          if not (List.mem t (ftv t'))
          then (apply_sub (t,t') state; reduce_typeclass_constraints state; unify state)
          else if TypeVar t <> t' then failwith (Printf.sprintf "cannot construct infinite type arising from constraint %s = %s" (string_of_var t) (string_of_type t')) else
            unify state
      )
      | (Fun(t1i,t1o),Fun(t2i,t2o),l,m) ->
          display_constraints state (Printf.sprintf "dealing with the constraint %s = %s that was inferred at %s because %s" (string_of_type (Fun(t1i,t1o))) (string_of_type (Fun(t2i,t2o))) (string_of_loc l) m);
          drop_equality ();
          add_type_equality state t1i t2i l (Printf.sprintf "because of earlier constraint %s = %s" (string_of_type (Fun(t1i,t1o))) (string_of_type (Fun(t2i,t2o))));
          add_type_equality state t1o t2o l (Printf.sprintf "because of earlier constraint %s = %s" (string_of_type (Fun(t1i,t1o))) (string_of_type (Fun(t2i,t2o))));
          unify state
      | (Product tlist1, Product tlist2,l,m) ->
          display_constraints state (Printf.sprintf "dealing with the constraint %s = %s that was inferred at %s because %s" (string_of_type (Product tlist1)) (string_of_type (Product tlist2)) (string_of_loc l) m);
          if (length tlist1) <> (length tlist2) then failwith (Printf.sprintf "cannot solve the constraint %s = %s because these are products of unequal length" (string_of_type (Product tlist1)) (string_of_type (Product tlist2)));
          drop_equality ();
          let _ = map (fun (t1,t2) -> add_type_equality state t1 t2 l (Printf.sprintf "because of earlier constraint %s = %s" (string_of_type (Product tlist1)) (string_of_type (Product tlist2)))) (zip tlist1 tlist2) in
          unify state
      | (SumType(type1,targs1), SumType(type2,targs2),l,m) ->
          display_constraints state (Printf.sprintf "dealing with the constraint %s = %s that was inferred at %s because %s" (string_of_type (SumType(type1,targs1))) (string_of_type (SumType(type2,targs2))) (string_of_loc l) m);
          drop_equality ();
          if type1 <> type2 then failwith (Printf.sprintf "cannot solve the constraint %s = %s" (string_of_type (SumType(type1,targs1))) (string_of_type (SumType(type2,targs2))));
          let _ = map (fun (t1,t2) -> add_type_equality state t1 t2 l (Printf.sprintf "because of earlier constraint %s = %s" (string_of_type (SumType(type1,targs1))) (string_of_type (SumType(type2,targs2))))) (zip targs1 targs2) in
          unify state
      | (t,t',l,m) ->
          display_constraints state (Printf.sprintf "dealing with the constraints %s = %s that was inferred at %s because %s\n" (string_of_type t) (string_of_type t') (string_of_loc l) m);
          if t = t' then (drop_equality (); unify state) else failwith (Printf.sprintf "cannot solve constraints %s = %s" (string_of_type t) (string_of_type t'))
  )
          

let reduce state =
  (* apply sub_so_far to all the constraints we have *)
  let _ = map (fun (v,tv) -> (!state).type_equalities := (map (fun (t1,t2,l,m) -> (tsub tv v t1, tsub tv v t2,l,m)) !((!state).type_equalities))) !((!state).sub_so_far) in
  !state.tracking := apply_sub_so_far state !(!state.tracking);
  !state.required_classes := map (fun (t,c,l,m) -> (apply_sub_so_far state t, c, l, m)) !(!state.required_classes);
  (* these updates are necessary because during typechecking we may have inferred stuff after these constraints were originally made *)
  reduce_typeclass_constraints state;
  unify state;
  display_constraints state "finished unification"


(* NOW START THE ACTUAL TYPECHECKING AREA *)

let rec gen_new_tvars state so_far t = 
  match t with
  | Integer -> Integer 
  | Floating -> Floating
  | Boolean -> Boolean
  | UnitType -> UnitType
  | Fun (a1,a2) -> Fun(gen_new_tvars state so_far a1, gen_new_tvars state so_far a2)
  | Product (alist) -> Product (map (gen_new_tvars state so_far) alist)
  | SumType (name,alist) -> SumType(name, map (gen_new_tvars state so_far) alist)
  | TypeVar (x) ->
      match assoc_opt x !so_far with
      | None ->(
      let fresh = get_fresh state in
      so_far := (x,fresh)::!so_far;
      let required = type_classes_of state x in
      (* fresh needs to have same required typeclasses as x did *)
      let _ = map (fun c -> add_type_class_required state (TypeVar fresh) c Lexing.dummy_pos (Printf.sprintf "%s is a clone of %s" (string_of_var fresh) (string_of_var x))) required in
      TypeVar (fresh)
      )
      | Some x' -> TypeVar x'

let rec instance_sub state t x e =
  let r = instance_sub state t x in
  match e with
  | IInt (_,_) -> e
  | IFloat (_,_) -> e
  | IBool (_,_) -> e
  | IVar (v,l) ->
      if v = x then
        let fresh_var = get_fresh state in
        let fresh_t = gen_new_tvars state (ref []) t in
        push_var_type state fresh_var fresh_t Lexing.dummy_pos (Printf.sprintf "%s is a clone of %s for polymorphism" (string_of_var fresh_var) (string_of_var x));
        IVar(fresh_var,l)
      else
        e
  | ILambda (e,x',a,l) -> if x <> x' then ILambda (r e, x', a, l) else ILambda (e, x', a, l)
  | IApplication (e1,e2,l) -> IApplication(r e1, r e2, l)
  | IIf(e1,e2,e3,l) -> IIf(r e1, r e2, r e3, l)
  | IUnit _ -> e
  | IPrint (e,l) -> IPrint (r e, l)
  | ISum (u,e,l) -> ISum(u,r e, l)
  | IProd (elist, l) -> IProd (map r elist, l)
  | IMatch (e, cases, l) -> IMatch (r e, map (fun (case,handler) -> (case, r handler)) cases, l)
  | IProj(e,n,i,l) -> IProj(r e, n, i, l)
  | INewSum (u, targs, defs, cont, l) -> INewSum (u, targs, defs, r cont, l)
  | ILet (x',a,e1,e2,l) ->
      if x' = x then
        ILet(x',a,r e1, e2, l)
      else
        ILet(x',a,r e1, r e2, l)
  | ILetRec (x',a,e1,e2,l) ->
      if x' = x then
        e
      else
        ILetRec (x', a, r e1, r e2, l)
  | INeg (e,l) -> INeg (r e, l)
  | IBinop (e1,b,e2,l) -> IBinop(r e1, b, r e2, l)


let binop_check state t1 b t2 l =
  match b with
  | Plus -> 
    display_state state l "this is a sum, so its args should be of the num typeclass, returning type equal to that of the first argument";
    add_type_class_required state t1 Number l "appears in + operation";
    add_type_class_required state t2 Number l "appears in + operation";
    add_type_equality state t1 t2 l "appear on opposite sides of + operation";
    t1
  | Times ->
    display_state state l "this is a product, so its args should be of the num typeclass, returning type equal to that of the first argument";
    add_type_class_required state t1 Number l "appears in * operation";
    add_type_class_required state t2 Number l "appears in * operation";
    add_type_equality state t1 t2 l "appear on opposite sides of * operation";
    t1
  | Subtract ->
    display_state state l "this is a subtraction, so its args should be of the num typeclass, returning type equal to that of the first argument";
    add_type_class_required state t1 Number l "appears in - operation";
    add_type_class_required state t2 Number l "appears in - operation";
    add_type_equality state t1 t2 l "appear on opposite sides of - operation";
    t1
  | Div ->
    display_state state l "this is a subtraction, so its args should be of the num typeclass, returning option type of the first argument";
    add_type_class_required state t1 Number l "appears in / operation";
    add_type_class_required state t2 Number l "appears in / operation";
    add_type_equality state t1 t2 l "appear on opposite sides of / operation";
    SumType("option", [t1])
  | Mod ->
    display_state state l "this is the mod operator so should have ints as args, returns type option int";
    add_type_equality state t1 Integer l "appears in a mod operation";
    add_type_equality state t2 Integer l "appears in a mod operation";
    SumType("option", [Integer])
  | L ->
    display_state state l "this is the < operator so should have ordered types as args, returns type bool";
    add_type_class_required state t1 Ordered l "appears in < operation";
    add_type_class_required state t2 Ordered l "appears in < operation";
    add_type_equality state t1 t2 l "appear in < operation with each other";
    Boolean 
  | G ->
    display_state state l "this is the > operator so should have ordered types as args, returns type bool";
    add_type_class_required state t1 Ordered l "appears in > operation";
    add_type_class_required state t2 Ordered l "appears in > operation";
    add_type_equality state t1 t2 l "appear in > operation with each other";
    Boolean 
  | Eq ->
    display_state state l "this is the = operator so should have eq types as args, returns type bool";
    add_type_class_required state t1 Equality l "appears in = operation";
    add_type_class_required state t2 Equality l "appears in = operation";
    add_type_equality state t1 t2 l "appear in = operation with each other";
    Boolean 
  | And ->
    display_state state l "this is the and operator so should have bools as args, returns type bool";
    add_type_equality state t1 Boolean l "appears in and operation";
    add_type_equality state t2 Boolean l "appears in and operation";
    Boolean 
  | Or ->
    display_state state l "this is the or operator so should have bools as args, returns type bool";
    add_type_equality state t1 Boolean l "appears in or operation";
    add_type_equality state t2 Boolean l "appears in or operation";
    Boolean 

let rec tcheck (state : state ref) = function
  | IBinop (e1,op,e2,l) ->
      let t1 = local_scope state e1 in
      let t2 = local_scope state e2 in
      binop_check state t1 op t2 l
  | IInt (_,l) ->
      display_state state l "this is an integer literal, so has type int";
      Integer
  | IFloat (_,l) ->
      display_state state l "this is a float literal, so has type float";
      Floating
  | IBool (_,l) ->
      display_state state l "this is a boolean literal, so has type bool";
      Boolean
  | IIf (e1,e2,e3,l) ->
      display_state state l "this is an if statement, so will make sure the guard is a bool and the two branches have equal type";
      let t1 = local_scope state e1 in
      let t2 = local_scope state e2 in
      let t3 = local_scope state e3 in
      add_type_equality state t1 Boolean l "appears as a guard in if statement";
      add_type_equality state t2 t3 l "these are types of two branches of if statement";
      t2
  | IApplication (e1,e2,l) ->
      display_state state l "this is an application, so will make sure the first expression is a function that can be applied to the second";
      let out_type = TypeVar(get_fresh state) in
      let t1 = local_scope state e1 in
      let t2 = local_scope state e2 in
      add_type_equality state t1 (Fun(t2,out_type)) l "this must be a function that takes in this type, output type was generated fresh";
      out_type
  | ILambda (e_body, arg_x, arg_t, l) ->
      display_state state l (Printf.sprintf "this is a function taking in the argument %s of type %s" (string_of_var arg_x) (string_of_annotation arg_t));
      push_var_type state arg_x (type_of_annotation arg_t) l (Printf.sprintf "the argument %s is bound to the type %s in the function definition" (string_of_var arg_x) (string_of_annotation arg_t));
      let t_body = local_scope state e_body in
      Fun(type_of_annotation arg_t,t_body)
  | IVar (x,l) ->(
      match lookup state x with
      | None -> display_state state l (Printf.sprintf "the variable %s is unbound" (string_of_var x)); failwith (Printf.sprintf "variable %s is unbound" (string_of_var x))
      | Some (t,l,m) ->
        display_state state l (Printf.sprintf "the variable %s has type %s, which was inferred at %s because %s" (string_of_var x) (string_of_type t) (string_of_loc l) m);
        t
        )
  | ILet (x,tx,e1,e2,l) ->
      display_state state l (Printf.sprintf "starting on this let statement");
      let t1 = local_scope state e1 in
      add_type_equality state t1 (type_of_annotation tx) l "the annotated and inferred type must be unified";
      (* determine the principal type *)
      !state.tracking := t1;
      reduce state;
      let pt = !(!state.tracking) in
      (*NOTE: this push is not necessary because after instance substitution it will not be needed. but for debugging purposes it is kind of nice for all these to be in there *)
      push_var_type state x pt l (Printf.sprintf "%s is bound to an expression of this type in a let statement" (string_of_var x));
      display_state state l (Printf.sprintf "got back a principal type of %s for the variable %s" (string_of_type pt) (string_of_var x));
      (match pt with
      | TypeVar _ ->
      tcheck state e2
      | _ ->
          if has_tv pt then let e2 = instance_sub state pt x e2 in tcheck state e2
          else tcheck state e2
      )
  | ILetRec (x,tx,e1,e2,l) ->
      display_state state l (Printf.sprintf "starting on this let statement");
      push_var_type state x (type_of_annotation tx) l (Printf.sprintf "%s is declared as recursive with this type annotation" (string_of_var x));
      let t1 = local_scope state e1 in
      pop_var_binding state;
      add_type_equality state t1 (type_of_annotation tx) l "the annotated and inferred type must be unified";
      (* determine the principal type *)
      !state.tracking := t1;
      reduce state;
      let pt = !(!state.tracking) in
      (*NOTE: this push is not necessary because after instance substitution it will not be needed. but for debugging purposes it is kind of nice for all these to be in there *)
      push_var_type state x pt l (Printf.sprintf "%s is bound to an expression of this type in a let statement" (string_of_var x));
      display_state state l (Printf.sprintf "got back a principal type of %s for the variable %s" (string_of_type pt) (string_of_var x));
      (match pt with
      | TypeVar _ ->
      tcheck state e2
      | _ ->
          if has_tv pt then let e2 = instance_sub state pt x e2 in tcheck state e2
          else tcheck state e2
      )
  | IUnit l ->
      display_state state l (Printf.sprintf "this is a unit literal, so has type unit");
      UnitType
  | ISum (u,e,l) -> 
      display_state state l (Printf.sprintf "this is a sumtype built with constructor %s" u);
      if not (is_cons state u) then failwith (Printf.sprintf "the constructor %s is not defined" u);
      let t = local_scope state e in
      (* lookup type associated with constructor u *)
      let t_name,t_args,def_list,l_def = entry_of_cons state u in
      let our_type = snd (find (fun (cons,_) -> cons = u) def_list) in
      (* generate new type variables for the targs of this type *)
      let fresh_t_args = map (fun _ -> get_fresh state) t_args in
      (* substitute into the type associated with constructor u *)
      let our_type = fold_left (fun acc (concrete,placeholder) -> tsub (TypeVar concrete) (Name placeholder) acc) our_type (zip fresh_t_args t_args) in
      (* add type equality between this type and t *)
      add_type_equality state t our_type l (Printf.sprintf "the expression of type %s is used as an argument to the constructor %s defined at %s which expects the type %s" (string_of_type t) u (string_of_loc l_def) (string_of_type our_type));
      (* return type that we found with the new type variables *)
      SumType(t_name, map (fun x -> TypeVar x) fresh_t_args)
  | INewSum (u,targs,def_list,cont,l) ->
      display_state state l (Printf.sprintf "this is a definition of a new type %s" u);
      if is_type state u then failwith (Printf.sprintf "the type %s already exists, and cannot be re-defined here" u);
      (
      match find_opt (fun x -> is_cons state x) (map (fun (x,_,_) -> x) def_list) with
        | Some cons -> failwith (Printf.sprintf "the constructor %s already exists, and cannot be re-defined here" cons)
        | _ ->
      let def_list = map (fun (x,y,_) -> (x,type_of_annotation y)) def_list in
      add_type state u targs def_list l;
      tcheck state cont
      )
  | IPrint (e,l) ->
      display_state state l "this is a print statement, will check that its argument is of the printable typeclass";
      let t = local_scope state e in
      add_type_class_required state t Printable l "print is applied to it";
      UnitType
  | INeg (e,l) ->
      display_state state l "this is a negation statement, will check that its argument is a number";
      let t = local_scope state e in
      add_type_class_required state t Number l "appears in a negation statement";
      t
  | IProj (e,i,n,l) ->
      display_state state l "this is a projection statement";
      if i >= n || i < 0 then failwith "index out of bounds";
      if n < 0 then display_failure l "this projection specifies it is for a negative length tuple, but there is no such thing";
      let rec generic_prod so_far n =
        if n = 0 then so_far
        else generic_prod ((TypeVar(get_fresh state))::so_far) (n-1)
      in
      let generic_prod = generic_prod [] n in
      let t = local_scope state e in
      add_type_equality state t (Product generic_prod) l (Printf.sprintf "based off of projection statement, this must be a product of length %n" n);
      nth generic_prod i 
  | IProd (elist,l) ->
      let n = length elist in
      display_state state l (Printf.sprintf "this is a tuple literal of length %n" n);
      let tlist = map (local_scope state) elist in
      Product tlist
  | IMatch (e,cases,l) ->
      display_state state l "working on this match statement";
      let t = local_scope state e in
      let out_type = TypeVar(get_fresh state) in
      match cases with
      | [] -> display_failure l "this match statement has no cases, which is not allowed"
      | (h,_)::_ ->(
      let (t_name,targs,def_list,_) = try entry_of_cons state h with _ -> display_failure l (Printf.sprintf "this match statement has first case %s but there is no such constructor" h) in
      display_state state l (Printf.sprintf "because the first case matched is %s, we have determined that this is matching on the type %s" h t_name);
      let fresh_targs = map (fun _ -> TypeVar(get_fresh state)) targs in
      let generic_expected = SumType(t_name,fresh_targs) in
      add_type_equality state t generic_expected l "this expression is being matched on with constructors coming from this sum type";
      (* TODO: add check to ensure cases are not duplicated *)
      if has_dups (map fst cases) then display_failure l "match statement has duplicate matches";
      (* TODO: give warnings if not all cases are matched *)
      let check_case : user_var_name * info_expr -> unit = function
      | (cons, handler) ->
        match find_opt (fun x -> fst x = cons) def_list with
        | None -> failwith (Printf.sprintf "the constructor %s is not defined for the type %s" cons t_name)
        | Some (_,t_def) ->
          let sub_map = (zip fresh_targs (map (fun x -> Name x) targs)) in
          let expected_type = fold_left (fun acc (inst,arg) -> tsub inst arg acc) t_def sub_map in
          let handler_type = local_scope state handler in
          add_type_equality state handler_type (Fun(expected_type,out_type)) l (Printf.sprintf "this is a handler of the %s case in a match statement" cons)
      in
      let _ = map check_case cases in out_type
      )
      

(* this helper typechecks e using tcheck but removes all newly bound variables after doing so *)
and local_scope state e =
  let rec help n =
    if n <= 0 then ()
    else (pop_var_binding state; help (n-1))
  in
  let init_stack_size = !(!state.depth_var_stack) in
  let result = tcheck state e in
  let num_local_bindings = !(!state.depth_var_stack) - init_stack_size in
  (if num_local_bindings < 0 then print_string "checkout local_scope function, somehow got negative number of local variable bindings"
  else help num_local_bindings);
  result

(* EXPORTED TYPECHECK FUNCTION*)
let add_print_def state e = 
  let fresh1 = get_fresh state in
  let fresh2 = get_fresh state in
  (ILet(Name "print", ATypeVar(fresh1,Lexing.dummy_pos), ILambda(IPrint (IVar (Name "x",Lexing.dummy_pos),Lexing.dummy_pos), Name "x", ATypeVar(fresh2,Lexing.dummy_pos), Lexing.dummy_pos),e,Lexing.dummy_pos))


let typecheck e fresh =
  let state = init_state fresh in
  let e = (add_print_def state e) in
  let result = tcheck state e in
  !state.tracking := result;
  reduce state;
  display_state state Lexing.dummy_pos "final state of constraints";
  let result = !(!state.tracking) in
    let free_tvars = ftv result in
    let class_constraints = filter (fun x -> mem (fst x) free_tvars) !(!state.known_classes) in
    let class_constrained_result = (result,class_constraints) in
    (class_constrained_result,strip (typed_expr_of_info_expr e), get_fresh state)
