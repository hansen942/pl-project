open Definitions

(** [info] should be line and column info *)
type info = int * int

(* [error_msg] tells what went wrong during type checking *)
type error_msg = string

(** [typecheck t_expr] either gives back [Right (t,e)] where [t] is the type of [t_expr] and [e] the expression with type annotations removed, or it gives back an [error_msg]*)
val typecheck : typed_expr -> var_name -> class_constrained_expr_type * sugar * var_name

type tconstraint =
| Equality of expr_type * expr_type
| TypeClass of expr_type * type_class
type constraints = tconstraint list

val string_of_constraints : constraints -> string

val strip : typed_expr -> sugar 
