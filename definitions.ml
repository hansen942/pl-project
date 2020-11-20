open List
(** This file contains all the shared types that the other modules need and also some functions that allow these types to be displayed.*)

(** users write programs where identifiers are strings *)
type user_var_name = string

(** [var_name] can use integers because this makes getting new variable names easier *)
type var_name =
| Sub of int
| Name of user_var_name 

(** [expr] is the type of our untyped expressions. It is essentially the applied lambda calculus. *)
and expr =
| Int of int
| Var of var_name
| Lambda of expr * var_name
| Application of expr * expr
| If of expr * expr * expr
| Bool of bool
| Plus of expr * expr
| Times of expr * expr
| Eq of expr * expr
| Unit
| Print of expr
| Sum of user_var_name * expr (* var_name is the constructor name used *)
| Prod of expr list
| Match of expr * ((user_var_name * expr) list)
| Proj of expr * int
(*| Lazy of expr ref*)

(*module Compare_VName : Map.OrderedType = struct
type t = var_name
let compare = compare 
end*)
(** [sugar] is supposed to represent syntactic sugar over the base language, however, sugar is somehwat a misnomer.
  This is because a properly typed program cannot contain [Z], the Z combinator, however during desugaring we introduce [Z] in the untyped base language when dealing with [LetRec] expressions.
  Dealing with the recursion in two different ways allows programs to type check even though they will be desugared to an untypeable program.
 It is worth noting here that let rec will act recursively on ALL expressions, not just functions, so that [let x = 1 in let rec x = x+1 in x] will not terminate, but [let x = 1 in let x = x+1 in x] will terminate and have value [2].
  *)
type sugar = 
| LetRec of var_name * sugar * sugar 
| Let of var_name * sugar * sugar 
| Z
| Base of expr

(** [z] is the Z-combinator *)
let z =
  let innermost = Lambda ( Application (Application (Var (Name "x"), Var (Name "x")), Var (Name "y")) , Name "y") in
  let lazy_omega' = Lambda (Application(Var (Name "f"), innermost), Name "x") in
  Lambda (Application (lazy_omega', lazy_omega'), Name "f") 

let rec desugar = function
| LetRec (v,e1,e2) -> Application (Lambda (desugar e2,v), Application(desugar Z, Lambda (desugar e1,v)))
| Let (v,e1,e2) -> Application (Lambda (desugar e2,v), desugar e1)
| Z -> z
| Base b -> b


let rec is_val = function
| Int _ -> true
| Bool _ -> true
| Lambda _ -> true
| Unit -> true
| Prod elist -> for_all is_val elist
| Sum (name,e) -> is_val e
| _ -> false

let rec naive_list_union' acc l1 = function
| h::t -> if mem h l1 then naive_list_union' acc l1 t else naive_list_union' (h::acc) l1 t
| [] -> acc @ l1

(** [list_union l1 l2] is a list that contains all the elements of [l1] and [l2] with no repeats, assuming that [l1] and [l2] also contain no repeats.
    Also note this is not tail recursive (because of use of [@] operator) and will have recursion depth = length of [l2]*)
let naive_list_union : 'a list -> 'a list -> 'a list = naive_list_union' []

(** [fv e] gives a list containing all the free variables of [e].
    Ideally, we would replace the list with a set but this requires defining an order on expressions so I'm just building it with lists first.
   if a projection will fail then it doesn't have any free variables*)
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
| Unit -> []
| Print e -> fv e
| Sum (name,e) -> fv e
| Prod elist -> fold_left (fun acc x -> naive_list_union acc (fv x)) [] elist
| Match (e,functions) ->
  naive_list_union (fv e) (fold_left (fun acc x -> naive_list_union acc (fv (snd x))) [] functions)
| Proj (expr,n) ->(
  match expr with
  | Prod elist -> (match nth_opt elist n with None -> [] | Some e -> fv e )
  | _ -> []
  )


let string_of_var v : string =
match v with
| Sub x -> Printf.sprintf "ⓥ %n" x
| Name v -> v

let rec string_of_expr : expr -> string = function
| Int n -> string_of_int n
| Var v -> string_of_var v
| Bool b -> string_of_bool b
| Eq (e1,e2) -> Printf.sprintf "%s = %s" (string_of_expr e1) (string_of_expr e2)
| Plus (e1,e2) -> Printf.sprintf "%s + %s" (string_of_expr e1) (string_of_expr e2)
| Times (e1,e2) -> Printf.sprintf "%s * (%s)" (string_of_expr e1) (string_of_expr e2)
| Lambda (e,arg) -> Printf.sprintf "λ%s.%s" (string_of_var arg) (string_of_expr e) 
| Application (e1,e2) -> Printf.sprintf "(%s) (%s)" (string_of_expr e1) (string_of_expr e2)
| If (e1,e2,e3) -> Printf.sprintf "if %s then %s else %s" (string_of_expr e1) (string_of_expr e2) (string_of_expr e3)
| Unit -> "()"
| Print e -> Printf.sprintf "print %s" (string_of_expr e)
| Sum (name,e) -> Printf.sprintf "%s %s" name (string_of_expr e)
| Prod elist ->(
  match elist with
  | [] -> "()"
  | h::t -> let body = (string_of_expr h) ^ (fold_left (fun acc x -> acc ^ ", " ^ (string_of_expr x)) "" t) in
  Printf.sprintf "(%s)" body
  )
| Match (e,cases) ->
  let body = fold_left (fun acc x -> acc ^ "| " ^ (fst x) ^ " -> " ^ (string_of_expr (snd x))) "" cases in
  Printf.sprintf "match %s with %s" (string_of_expr e) body
| Proj (e,n) -> Printf.sprintf "%s[%s]" (string_of_expr e) (string_of_int n)
 
let rec string_of_sugar : sugar -> string = function
| Let (v,e1,e2) -> Printf.sprintf "let %s = %s in %s" (string_of_var v) (string_of_sugar e1) (string_of_sugar e2)
| LetRec (v,e1,e2) -> Printf.sprintf "let rec %s = %s in %s" (string_of_var v) (string_of_sugar e1) (string_of_sugar e2)
| Z -> "Z"
| Base e -> string_of_expr e

(** [type_class] serves the purpose of telling what generic types can have generic operations done on them *)
type type_class =
| Printable

let string_of_typeclass = function
| Printable -> "printable"

type class_constraints = type_class list

(** [expr_type] is the type of types in our language. Hopefully we will extend this to include user-defined types as well.*)
type expr_type =
| Integer
| Boolean
| Fun of expr_type * expr_type
| UnitType
| TypeVar of var_name
| Product of expr_type list
| SumType of user_var_name * ((user_var_name * expr_type) list)
(*TODO: these extensions*)
(*
and user_type =
| Sum of user_var_name * ((user_var_name * (expr_type list)) list)
| NamedProd of user_var_name * (expr_type list)
| Prod of expr_type list
| User of user_type
*)

let rec ftv = function
| Fun (t1,t2) ->
  let ft1v = ftv t1 in 
  let ft2v = ftv t2 in
  naive_list_union ft1v ft2v
| Integer -> []
| Boolean -> []
| UnitType -> []
| TypeVar v -> [v]
| Product tlist -> fold_left (fun acc x -> naive_list_union acc (ftv x)) [] tlist
| SumType (name,constructors) -> fold_left (fun acc x -> naive_list_union acc (ftv (snd x))) [] constructors

let rec tsub t_new tvar = fun t ->
  match t with
  | TypeVar v -> if v = tvar then t_new else t
  | Fun (t1,t2) ->
    Fun (tsub t_new tvar t1, tsub t_new tvar t2)
  | Product tlist -> Product (map (tsub t_new tvar) tlist)
  | SumType (name,constructors) -> SumType (name,(map (fun (c,ct)-> (c,tsub t_new tvar ct)) constructors))
  | _ -> t

let rec string_of_type = function
| Integer -> "int"
| Boolean -> "bool"
| Fun (t1,t2) ->
  let s1 =
    match t1 with
    | Fun _ -> Printf.sprintf "(%s)" (string_of_type t1)
    | _ -> string_of_type t1
  in
  Printf.sprintf "%s →  %s" s1 (string_of_type t2)
| UnitType -> "unit"
| SumType (name,constructors) ->
  let cons_strings = map (fun (c,ct) -> c ^ " " ^ (string_of_type ct)) constructors in
  name ^ " = " ^
  (match cons_strings with
  | [] -> "void"
  | h::t -> "sum " ^ h ^ (fold_left (fun acc x -> "| " ^ x)) "" t
  )
| Product tlist ->
  let entries = map string_of_type tlist in
  (match entries with
  | [] -> "EmptyProduct"
  | h::[] -> Printf.sprintf "unary product %s" h
  | h::t -> h ^ (fold_left (fun acc x -> acc ^ " * " ^ x) "" t)
  )
| TypeVar v -> Printf.sprintf "%s" (string_of_var v)

(** [known_classes] is an association list, if [(a,[c1,c2,c3])] is in the list this means that we know [a] is in the type classes [c1,c2,c3]. *)
type known_classes = (var_name * class_constraints) list

type class_constrained_expr_type = expr_type * known_classes

let string_of_tvar_constraint v = function
  | c::[] -> Printf.sprintf "∀ %s %s." (string_of_typeclass c) (string_of_var v)
  | [] -> Printf.sprintf "∀ %s." (string_of_var v)
  | lst ->
    let cons_string = fold_left (fun acc x -> acc ^ ", " ^ string_of_typeclass x) "" lst in
    Printf.sprintf "∀ (%s) %s." cons_string (string_of_var v)

(** this gives string for the type and class constraints associated *)
let string_of_class_constrained_expr_type = function
  | (t,kc) -> let kc_needed = filter (fun x -> mem (fst x) (ftv t)) kc in
    let quantifiers = fold_left (fun acc x -> acc ^ " " ^ (string_of_tvar_constraint (fst x) (snd x))) "" kc_needed in
    Printf.sprintf "%s%s" quantifiers (string_of_type t)

(** Elements of [typed_expr] represent expressions which are annotated with types.*)
type typed_expr =
| TInt of int
| TBool of bool
| TVar of var_name
| TPlus of typed_expr * typed_expr
| TTimes of typed_expr * typed_expr
| TLambda of typed_expr * var_name * expr_type
| TApplication of typed_expr * typed_expr
| TIf of typed_expr * typed_expr * typed_expr
| TEq of typed_expr * typed_expr
| TUnit
| TPrint of typed_expr
| TSum of user_var_name * typed_expr (* var_name is the constructor name used *)
| TProd of typed_expr list
| TMatch of typed_expr * ((user_var_name * typed_expr) list)
| TProj of typed_expr * int * int (* index you want, length of tuple you expect *)
(* for type inference purposes it is important we know the length of the tuple in advance. We would not have this problem if we instead only allowed pairs and wrote n-tuples as nested pairs, but that's just silly. In effect you can think of this as being a dependently typed function whose second argument determines the type, but because these are constants it doesn't require any extra work. Note that the args are printed in the other order*)

let rec string_of_typed_expr : typed_expr -> string = function
| TInt n -> string_of_int n
| TVar v -> string_of_var v
| TBool b -> string_of_bool b
| TEq (e1,e2) -> Printf.sprintf "%s = %s" (string_of_typed_expr e1) (string_of_typed_expr e2)
| TPlus (e1,e2) -> Printf.sprintf "%s + %s" (string_of_typed_expr e1) (string_of_typed_expr e2)
| TTimes (e1,e2) -> Printf.sprintf "%s * (%s)" (string_of_typed_expr e1) (string_of_typed_expr e2)
| TLambda (e,arg,t) -> Printf.sprintf "λ%s : %s.%s" (string_of_var arg) (string_of_type t) (string_of_typed_expr e) 
| TApplication (e1,e2) -> Printf.sprintf "(%s) (%s)" (string_of_typed_expr e1) (string_of_typed_expr e2)
| TIf (e1,e2,e3) -> Printf.sprintf "if %s then %s else %s" (string_of_typed_expr e1) (string_of_typed_expr e2) (string_of_typed_expr e3)
| TUnit -> "()"
| TPrint e -> (Printf.sprintf "print %s" (string_of_typed_expr e))
| TSum (name,expr) -> Printf.sprintf "%s %s" name (string_of_typed_expr expr)
| TProd elist ->(
  match elist with
  | [] -> "()"
  | h::t -> let body = (string_of_typed_expr h) ^ (fold_left (fun acc x -> acc ^ ", " ^ (string_of_typed_expr x)) "" t) in
  Printf.sprintf "(%s)" body
  )
| TMatch (e,cases) ->
  let body = fold_left (fun acc x -> acc ^ "| " ^ (fst x) ^ " -> " ^ (string_of_typed_expr (snd x))) "" cases in
  Printf.sprintf "match %s with %s" (string_of_typed_expr e) body
| TProj (e,n,l) -> Printf.sprintf "proj %s %s %s" (string_of_int l) (string_of_int n) (string_of_typed_expr e) 

(* allow user to define new types so they can actually use sums *)
(** [typed_sugar] is a sugary version of [typed_expr].
    The idea is that [typed_sugar] keeps track of where [let] and [let rec] are used. *)
type typed_sugar =
| NewSum of user_var_name * (user_var_name list) * (user_var_name * expr_type) list * typed_sugar (* new type name, type variables used, constructors by types, next expression *)
| TLet of var_name * typed_sugar * typed_sugar
| TLetRec of var_name * expr_type * typed_sugar * typed_sugar
| TBase of typed_expr

let quick_strip_tsugar = function
| TBase e -> e
| _ -> failwith "cannot strip let expressions"

let rec string_of_typed_sugar : typed_sugar -> string = function
| NewSum (name,vars,cons,s) ->(
  let bind_vars = fold_right (fun x acc -> x ^ " " ^ acc) vars "" in
  match cons with
  | [] -> Printf.sprintf "%s = void" name
  | h::t -> let body = match h with (ch,th) -> ch ^ " " ^ (string_of_type th) ^ (fold_right (fun (c,t) acc -> (Printf.sprintf " | %s %s" c (string_of_type t)) ^ acc) t "") in
  let dec = Printf.sprintf "newtype %s %s = %s" name bind_vars body in
  Printf.sprintf "%s in %s" dec (string_of_typed_sugar s)
  )
| TLet (v,e1,e2) -> Printf.sprintf "let %s = %s in %s" (string_of_var v) (string_of_typed_sugar e1) (string_of_typed_sugar e2)
| TLetRec (v,tv,e1,e2) -> Printf.sprintf "let rec %s : %s = %s in %s" (string_of_var v) (string_of_type tv) (string_of_typed_sugar e1) (string_of_typed_sugar e2)
| TBase e -> string_of_typed_expr e

(* Note: for type variables you should check the known type class constraints to see if it is declared prinatble before calling this. *)
let rec printable : expr_type -> bool = function
| UnitType -> true
| Integer -> true
| Boolean -> true
| Fun _ -> false
| SumType (name,cons) -> for_all printable (map snd cons)
| Product tlist -> for_all printable tlist
| TypeVar _ -> false

(* these types only have optional type annotations *)
type opt_t_expr = 
| OInt of int
| OBool of bool
| OVar of var_name
| OPlus of opt_t_expr * opt_t_expr 
| OTimes of opt_t_expr * opt_t_expr
| OLambda of opt_t_expr * var_name * (expr_type option)
| OApplication of opt_t_expr * opt_t_expr
| OIf of opt_t_expr * opt_t_expr * opt_t_expr
| OEq of opt_t_expr * opt_t_expr
| OUnit
| OPrint of opt_t_expr
| OSum of user_var_name * opt_t_expr
| OProd of opt_t_expr list
| OMatch of opt_t_expr * ((user_var_name * opt_t_expr) list)
| OProj of opt_t_expr * int * int

type opt_t_sugar =
| ONewSum of user_var_name * (user_var_name list) * (user_var_name * expr_type) list * opt_t_sugar (* new type name, type variables used, constructors by types *)
| OLet of var_name * opt_t_sugar * opt_t_sugar 
| OLetRec of var_name * (expr_type option) * opt_t_sugar * opt_t_sugar 
| OBase of opt_t_expr 

type ('a,'s) state = 's -> ('a * 's)
let return x = fun s -> (x,s)
(* this is standard bind *) 
let (>>=) (init_state:('a,'s) state) (transform:'a -> ('b,'s) state) =
  (fun old_state ->
  let first_val, first_state = init_state old_state in
  transform first_val first_state
  )
let (let*) x f = x >>= f

let init_name = Sub 0
let pull_name = function
| Sub n -> (Sub n, Sub (n+1))
| _ -> failwith "internal error" 

let rec annotate_opt_t_expr' oexpr =
  let f = annotate_opt_t_expr' in
  match oexpr with
  | OInt n -> return(TInt n)
  | OBool b -> return(TBool b)
  | OVar v -> return(TVar v)
  | OPlus(e1,e2) ->
    let* e1' = f e1 in
    let* e2' = f e2 in
    return(TPlus(e1',e2'))
  | OTimes(e1,e2) ->
    let* e1' = f e1 in
    let* e2' = f e2 in
    return(TTimes(e1',e2'))
  | OLambda(e1,v,t_opt) ->
    let* e1' = f e1 in
    let* t =
    match t_opt with
    | Some t -> return t
    | None -> let* name = pull_name in return(TypeVar(name))
    in
    return(TLambda(e1',v,t))
  | OApplication(e1,e2) ->
    let* e1' = f e1 in
    let* e2' = f e2 in
    return(TApplication(e1',e2'))
  | OIf(e1,e2,e3) ->
    let* e1' = f e1 in
    let* e2' = f e2 in
    let* e3' = f e3 in
    return(TIf(e1',e2',e3'))
  | OEq(e1,e2) ->
    let* e1' = f e1 in
    let* e2' = f e2 in
    return(TEq(e1',e2'))
  | OPrint(e) ->
    let* e' = f e in
    return(TPrint(e'))
  | OSum(name,e) ->
    let* e' = f e in
    return(TSum(name,e'))
  | OProd(elist) ->
    let* elist' = fold_right (fun x acc -> let* x' = f x in let* acc' = acc in return(x'::acc')) elist (return []) in
    return(TProd(elist'))
  | OMatch(e,cases) ->
    let* e' = f e in
    let* cases' = fold_right (fun (cons,e) acc -> let* e' = f e in let* acc' = acc in return((cons,e')::acc')) cases (return []) in
    return(TMatch(e',cases'))
  | OProj(e,i,l) ->
    let* e' = f e in
    return(TProj(e',i,l))

let rec annotate_opt_t_sugar sug =
  let g = annotate_opt_t_sugar in
  let f = annotate_opt_t_expr' in
  match sug with
  | OLet(v,e1,e2) ->
    let* e1' = g e1 in
    let* e2' = g e2 in
    return(TLet(v,e1',e2'))
  | OLetRec(v,t_opt,e1,e2) ->
    let* t =
    match t_opt with
    | None -> let* name = pull_name in return(TypeVar(name))
    | Some t -> return t
    in
    let* e1' = g e1 in
    let* e2' = g e2 in
    return(TLetRec(v,t,e1',e2'))
  | OBase(e) -> let* e' = f e in return(TBase e')
  | ONewSum (w,x,y,z) -> let* z' = g z in return(NewSum (w,x,y,z')) 
