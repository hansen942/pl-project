open Definitions
(** the [either] monad allows us to express failure in a principled way*)
type ('a,'b) either = Left of 'a | Right of 'b

val return : 'a -> ('b,'a) either

val (>>=) : ('a,'b) either -> ('b -> ('a,'c) either) -> ('a,'c) either

val (let*) : ('a,'b) either -> ('b -> ('a,'c) either) -> ('a,'c) either

(** [info] should be line and column info *)
type info = int * int

(* [error_msg] tells what went wrong during type checking *)
type error_msg = string

(** [typecheck t_expr] either gives back [Right (t,e)] where [t] is the type of [t_expr] and [e] the expression with type annotations removed, or it gives back an [error_msg]*)
val typecheck : typed_sugar -> class_constrained_expr_type * sugar

type tconstraint =
| Equality of expr_type * expr_type
| TypeClass of expr_type * type_class
type constraints = tconstraint list

val string_of_constraints : constraints -> string

val tcheck_simple_test : typed_expr -> class_constrained_expr_type
val print_sub_map : (var_name * expr_type) list -> unit

