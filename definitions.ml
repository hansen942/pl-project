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
(*| Lazy of expr ref*)

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

let rec string_of_sugar : sugar -> string = function
| Let (v,e1,e2) -> Printf.sprintf "let %s = %s in %s" (string_of_var v) (string_of_sugar e1) (string_of_sugar e2)
| LetRec (v,e1,e2) -> Printf.sprintf "let rec %s = %s in %s" (string_of_var v) (string_of_sugar e1) (string_of_sugar e2)
| Z -> "Z"
| Base e -> string_of_expr e

(** [expr_type] is the type of types in our language. Hopefully we will extend this to include user-defined types as well.*)
type expr_type =
| Integer of int
| Boolean of bool
| Fun of expr_type * expr_type
| Unit
(*TODO: these extensions*)
(*| Prod of expr_type list
| User of user_type

and user_type =
| Sum of user_var_name * ((user_var_name * (expr_type list)) list)
| NamedProd of user_var_name * (expr_type list)
*)

(** Elements of [typed_expr] represent expressions which are annotated with types.
    The only weird definition is that of [TVar] which allows an optional type annotation.
    This is so that when we desugar from a [typed_sugar] we can avoid putting in the Z
    combinators and all recursive references will be annotated with the type that they will
    have explicitly (since otherwise they would look like unbound variables)*)
type typed_expr =
| TInt of int
| TBool of bool
| TVar of var_name * (expr_type option)
| TPlus of typed_expr * typed_expr
| TTimes of typed_expr * typed_expr
(*| TVar of var_name*)
| TLambda of typed_expr * var_name * expr_type
| TApplication of typed_expr * typed_expr
| TIf of typed_expr * typed_expr * typed_expr

(** [typed_sugar] is a sugary version of [typed_expr].
    The idea is that [typed_sugar] keeps track of where [let] and [let rec] are used so that we can have the following workflow: [typed_sugar] is desugared into a [typed_expr] (throwing away the [let recs] and giving all recursively referenced variables the type of the binder they should have) which is type checked. If it passes we want to evaluate, so the original [typed_sugar] is stripped of type annotations to become a regular [sugar], which can then be evaluated.*)
type typed_sugar =
| TLet of var_name * typed_expr * typed_expr
| TLetRec of var_name * typed_expr * typed_expr
| TBase of typed_expr


(** [def] is the type of a definition. The idea is that we have a list of definitions of both types and values before a final expression that gives the programs result. But we have not implemented user-defined types yet. *)
type 'a def =
| Value of user_var_name * 'a 
| NewSum of user_var_name * ((user_var_name * (expr_type list)) list)
| NewProd of user_var_name * (expr_type list)

type prog = ((typed_expr def) list) * (typed_expr option)
