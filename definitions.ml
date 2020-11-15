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


let is_val = function
| Int _ -> true
| Bool _ -> true
| Lambda _ -> true
| Unit -> true
| _ -> false

let rec naive_list_union' acc l1 = function
| h::t -> if mem h l1 then naive_list_union' acc l1 t else naive_list_union' (h::acc) l1 t
| [] -> acc @ l1

(** [list_union l1 l2] is a list that contains all the elements of [l1] and [l2] with no repeats, assuming that [l1] and [l2] also contain no repeats.
    Also note this is not tail recursive (because of use of [@] operator) and will have recursion depth = length of [l2]*)
let naive_list_union : 'a list -> 'a list -> 'a list = naive_list_union' []

(** [fv e] gives a list containing all the free variables of [e].
    Ideally, we would replace the list with a set but this requires defining an order on expressions so I'm just building it with lists first.*)
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

let rec tsub t_new tvar = fun t ->
  match t with
  | TypeVar v -> if v = tvar then t_new else t
  | Fun (t1,t2) ->
    Fun (tsub t_new tvar t1, tsub t_new tvar t2)
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
| TypeVar v -> Printf.sprintf "Tvar %s" (string_of_var v)

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
    
    

(* Use Simple if there are no type variables, use quantified if there are.
   Using this setup ensures it is not possible to write anything but prenex quantifiers.*)
type tscheme = Simple of expr_type | Quantified of known_classes * expr_type



(** Elements of [typed_expr] represent expressions which are annotated with types.*)
type typed_expr =
| TInt of int
| TBool of bool
| TVar of var_name
| TPlus of typed_expr * typed_expr
| TTimes of typed_expr * typed_expr
| TLambda of typed_expr * var_name * expr_type
(*| QTLambda of typed_expr * var_name * expr_type * class_constraints*)
| TApplication of typed_expr * typed_expr
| TIf of typed_expr * typed_expr * typed_expr
| TEq of typed_expr * typed_expr
| TUnit
| TPrint of typed_expr

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

(** [typed_sugar] is a sugary version of [typed_expr].
    The idea is that [typed_sugar] keeps track of where [let] and [let rec] are used. *)
type typed_sugar =
| TLet of var_name * typed_sugar * typed_sugar
| TLetRec of var_name * expr_type * typed_sugar * typed_sugar
| TBase of typed_expr

let rec string_of_typed_sugar : typed_sugar -> string = function
| TLet (v,e1,e2) -> Printf.sprintf "let %s = %s in %s" (string_of_var v) (string_of_typed_sugar e1) (string_of_typed_sugar e2)
| TLetRec (v,tv,e1,e2) -> Printf.sprintf "let rec %s : %s = %s in %s" (string_of_var v) (string_of_type tv) (string_of_typed_sugar e1) (string_of_typed_sugar e2)
| TBase e -> string_of_typed_expr e

(*TODO: change the case with typevariables to do something better than this. Ideally should use the constrained_type type to infer if printable *)
let printable : expr_type -> bool = function
| UnitType -> true
| Integer -> true
| Boolean -> true
| Fun _ -> false
| TypeVar _ -> false
(** [def] is the type of a definition. The idea is that we have a list of definitions of both types and values before a final expression that gives the programs result. But we have not implemented user-defined types yet. *)
type 'a def =
| Value of user_var_name * 'a 
| NewSum of user_var_name * ((user_var_name * (expr_type list)) list)
| NewProd of user_var_name * (expr_type list)

type prog = ((typed_expr def) list) * (typed_expr option)
