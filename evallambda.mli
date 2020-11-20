open Definitions
(** [eval e] gives the value that [e] evaluates to. Will never terminate if [e] does not terminate. *)
val eval : expr -> var_name -> expr
