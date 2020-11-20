open Definitions
open Typecheck
open Evallambda

let init_name = Sub 0

let filename = ref ""
let nocheck = ref false

(** [run_prog] first typechecks its input, then evaluates it*)
let run_prog tsugar init_name =
  let t,e = typecheck tsugar init_name in
  if !nocheck then () else
  print_endline (string_of_class_constrained_expr_type t);
  eval (desugar e)


let options = [
  "-nocheck", Arg.Unit (fun _ -> nocheck := true), "Disable type checker"
]

let _ =
  (* (1) Parse the command-line arguments. *)
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
  (* fill in empty annotations, and for now just print expression *)
  match annotate_opt_t_sugar e init_name with
  (tsug, name) -> run_prog tsug name
  


