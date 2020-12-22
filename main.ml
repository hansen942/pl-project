open Definitions
open Typecheck
open Evallambda

let filename = ref ""

(** [run_prog] first typechecks its input, then evaluates it*)
let run_prog tsugar fresh =
  file := !filename;
  let t,e,fresh = typecheck tsugar fresh in
  print_newline ();
  print_endline "finished running typechecker!";
  Printf.printf "got type %s\n" (string_of_class_constrained_expr_type t);
  let basic = desugar e in
  print_endline "running evaluator now";
  flush stdout;
  eval basic fresh
  (*
  print_endline (string_of_class_constrained_expr_type t);
  eval (desugar e)
  *)

let options = [
  "-debug", Arg.Unit (fun _ -> Typecheck.debug := true), "turn on the debug output of the typechecker"
]


let _ =
  (* (1) Get the input source file. *)
  let usage_msg = Format.sprintf "Usage: %s [opts] <file>\n" Sys.argv.(0) in
  let _ = begin
    Arg.parse options (fun f ->
      if !filename = "" then filename := f else Arg.usage options usage_msg
    ) usage_msg;
    if !filename = "" then (Arg.usage options usage_msg; exit 1);
  end in

  (* (2) Parse the file to an expression. *)
  let file = open_in (!filename) in
  let lexbuf = Lexing.from_channel file in
  let e =
    try Parser.prog Lexer.token lexbuf
    with Parsing.Parse_error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Format.printf "Syntax error at %d:%d\n"
        pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol);
      exit 1 in
  let fresh = ref (Sub 0) in
  let filled_in = info_of_from_parser fresh e in
  run_prog filled_in fresh
  (* fill in empty annotations, and for now just print expression *)
  (*match annotate_opt_t_expr e init_name with
  (tsug, name) -> run_prog tsug name*)
