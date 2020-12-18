open Definitions


(** [typecheck t_expr name] either gives back [(t,e,name_out)] where [t] is the type of [t_expr] (a class constrained type, which is a type and possibly type class constraints), [e] is the expression with type annotations removed, and [name_out] is the next fresh name that has not been used as a type variable, or throws an error because the expression is not well-typed. The argument [name] is the next name that has not so far been used as a type variable (before type checking).*)
val typecheck : typed_expr -> var_name -> class_constrained_expr_type * sugar * var_name

(*type tconstraint =
| Equality of expr_type * expr_type
| TypeClass of expr_type * type_class
type constraints = tconstraint list

val string_of_constraints : constraints -> string
*)

(** [stip e] gives back the expression [e] but with all type annotations removed. *)
val strip : typed_expr -> sugar 
