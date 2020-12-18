open Definitions
open List

let file = ref "print_squares.evco"

(* DEFINE THE STATE OF THE TYPECHECKER AND SOME ASSOCIATED HELPERS *)
type state = {
  type_equalities : ((expr_type * expr_type) list) ref;
  known_classes : (var_name * (type_class list)) list ref;
  required_classes : (expr_type * type_class) list ref;
  variable_types : (var_name * expr_type) list ref;
  fresh_var : var_name ref
} 

let init_state = ref {
  type_equalities = ref [];
  known_classes = ref [];
  required_classes = ref[];
  variable_types = ref [];
  fresh_var = ref (Sub 0)
}

let add_type_equality state t1 t2 =
  (!state.type_equalities) := (t1,t2) :: !(!state.type_equalities)

(* DEFINE A BUNCH OF STUFF TO PRINT OUT THE STATE OF THE TYPECHECKER *)
(* change to false to avoid printouts *)
let debug = true

let display filename location =
  let file = open_in filename in
  let lexbuf = Lexing.from_channel file in
  Visualizer.print_out location lexbuf

let display_buf = Buffer.create 256

let string_of_type_equalities type_equalities =
  fold_left (fun acc (x,y) -> acc^Printf.sprintf "%s = %s\n" (string_of_type x) (string_of_type y)) "" !type_equalities

let string_of_required_classes required_classes =
  fold_left (fun acc (x,y) -> acc^Printf.sprintf "%s %s\n" (string_of_typeclass y) (string_of_type x)) "" !required_classes

let string_of_known_classes class_constraints =
  let string_of_multi_classes classes =
    match classes with
    | [] -> failwith "should not call string_of_known_classes on unconstrainted variable"
    | [c] -> string_of_typeclass c
    | h::t -> Printf.sprintf "(%s)" (fold_left (fun acc x -> acc^", "^(string_of_typeclass x)) (string_of_typeclass h) t)
  in
  fold_left (fun acc (x,y) -> acc^Printf.sprintf "%s %s\n" (string_of_multi_classes y) (string_of_var x)) "" !class_constraints

let string_of_venv venv =
  fold_left (fun acc (x,y) -> acc^Printf.sprintf "%s %s\n" (string_of_var x) (string_of_type y)) "" !venv


let string_of_state state =
  let string_equalities = string_of_type_equalities state.type_equalities in
  let string_known = string_of_known_classes state.known_classes in
  let string_required = string_of_required_classes state.required_classes in
  let string_venv = string_of_venv state.variable_types in
  let string_fresh = string_of_var !(state.fresh_var) in
  let divider = (String.make 80 '=') in
  Printf.sprintf "Constraints\n%s\n%s%s%sVariable Environment\n%s\n%s%s\nNext Fresh Variable: %s\n" divider string_equalities string_known string_required divider string_venv divider string_fresh

let reset_display buf =
  Buffer.reset buf;
  Buffer.add_string buf "\x1b[2J\x1b[H";
  Buffer.output_buffer stdout buf;
  flush stdout

let display_state state loc msg =
  if debug then
  reset_display display_buf;
  Buffer.add_string display_buf (string_of_state !state);
  Buffer.output_buffer stdout display_buf;
  display (!file) loc;
  print_newline ();
  print_string msg

let _ = display_state init_state {pos_fname = !file; pos_lnum = 6; pos_cnum = 3; pos_bol = 0} "This is a test!"

(* NOW START THE ACTUAL TYPECHECKING AREA *)

let rec tcheck (state : state ref) = function
  | IBinop (e1,op,e2,l) ->(
      match op with
      | Plus ->
          let t1 = tcheck state e1 in
          let t2 = tcheck state e2 in
          add_type_equality state t1 Integer;
          add_type_equality state t2 Integer;
          display_state state l "Added constraints that these two terms are integers.";
          Integer
      | _ -> failwith "unimplemented"
    )
  | _ -> failwith "unimplemented"

let typecheck _ = failwith "unimplemented"
