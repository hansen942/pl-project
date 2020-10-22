(** users write programs where identifiers are strings *)
type user_var_name = string

(** [var_name] can use integers because this makes getting new variable names easier *)
type var_name =
| Sub of int
| Name of user_var_name 

(** [expr_type] is the type of types in our language. Atomic represents a type corresponding to a closure and so *)
type expr_type =
| Integer of int
| Boolean of bool
| Fun of expr_type * expr_type
| Prod of expr_type list
| User of user_type

and user_type =
| Sum of user_var_name * ((user_var_name * (expr_type list)) list)
| NamedProd of user_var_name * (expr_type list)

(** [def] is the type of a definition. These are used to update the environment before evaluating the program's main expression, if one exists. *)
type 'a def =
| Value of user_var_name * 'a 
| NewSum of user_var_name * ((user_var_name * (expr_type list)) list)
| NewProd of user_var_name * (expr_type list)

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
| Z
(*| Lazy of expr ref*)

type typed_expr =
| TInt of int
| TBool of bool
| TPlus of typed_expr * typed_expr
| TTimes of typed_expr * typed_expr
| TClosure of typed_expr ref
| TVar of var_name
| TLambda of typed_expr * var_name * expr_type
| TApplication of typed_expr * typed_expr
| TIf of typed_expr * typed_expr * typed_expr


type prog = ((typed_expr def) list) * (typed_expr option)

let is_val = function
| Int _ -> true
| Bool _ -> true
| Lambda _ -> true
| _ -> false

let string_of_var v : string =
match v with
| Sub x -> Printf.sprintf "sub variable %n" x
| Name v -> v

let rec string_of_expr : expr -> string = function
| Z -> "Z"
| Int n -> string_of_int n
| Var v -> string_of_var v
| Bool b -> string_of_bool b
| Eq (e1,e2) -> Printf.sprintf "%s = %s" (string_of_expr e1) (string_of_expr e2)
| Plus (e1,e2) -> Printf.sprintf "%s + %s" (string_of_expr e1) (string_of_expr e2)
| Times (e1,e2) -> Printf.sprintf "%s * (%s)" (string_of_expr e1) (string_of_expr e2)
| Lambda (e,arg) -> Printf.sprintf "λ%s.%s" (string_of_var arg) (string_of_expr e) 
| Application (e1,e2) -> Printf.sprintf "(%s) (%s)" (string_of_expr e1) (string_of_expr e2)
| If (e1,e2,e3) -> Printf.sprintf "if %s then %s else %s" (string_of_expr e1) (string_of_expr e2) (string_of_expr e3)

(** [z] is the Z-combinator *)
let innermost = Lambda ( Application (Application (Var (Name "x"), Var (Name "x")), Var (Name "y")) , Name "y")
let _ = Printf.printf "currently have innermost = %s" (string_of_expr innermost); print_newline ()
let lazy_omega' = Lambda (Application(Var (Name "f"), innermost), Name "x")
let _ = Printf.printf "currently have lazy_omega' = %s" (string_of_expr lazy_omega'); print_newline ()
let z = Lambda (Application (lazy_omega', lazy_omega'), Name "f") 
let _ = Printf.printf "currently have z = %s" (string_of_expr z); print_newline ()
