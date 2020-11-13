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

(** [expr_type] is the type of types in our language. Hopefully we will extend this to include user-defined types as well.*)
type expr_type =
| Integer
| Boolean
| Fun of expr_type * expr_type
| UnitType
(*TODO: these extensions*)
(*| Prod of expr_type list
| User of user_type

and user_type =
| Sum of user_var_name * ((user_var_name * (expr_type list)) list)
| NamedProd of user_var_name * (expr_type list)
*)

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

(** Elements of [typed_expr] represent expressions which are annotated with types.*)
type typed_expr =
| TInt of int
| TBool of bool
| TVar of var_name
| TPlus of typed_expr * typed_expr
| TTimes of typed_expr * typed_expr
(*| TVar of var_name*)
| TLambda of typed_expr * var_name * expr_type
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

let printable : expr_type -> bool = function
| UnitType -> true
| Integer -> true
| Boolean -> true
| Fun _ -> false

(** [def] is the type of a definition. The idea is that we have a list of definitions of both types and values before a final expression that gives the programs result. But we have not implemented user-defined types yet. *)
type 'a def =
| Value of user_var_name * 'a 
| NewSum of user_var_name * ((user_var_name * (expr_type list)) list)
| NewProd of user_var_name * (expr_type list)

type prog = ((typed_expr def) list) * (typed_expr option)
