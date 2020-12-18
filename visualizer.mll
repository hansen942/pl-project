{
open Printf
open Lexing
exception Eof
exception Err
let first_line pos = pos.pos_lnum - 5
let last_line pos = pos.pos_lnum + 5
let out_char c lexbuf pos =
  let currline = lexbuf.Lexing.lex_curr_p.pos_lnum in if currline >= first_line pos && currline <= last_line pos then print_char c
let show_place pos =
  let num_spaces = (pos.pos_cnum - pos.pos_bol - 1) in
          print_string (String.make num_spaces ' ');
          print_char '^';
          print_endline ""
}

rule print_out pos = parse
| '\n' { Lexing.new_line lexbuf;
        out_char '\n' lexbuf pos;
        (if (lexbuf.lex_curr_p.pos_lnum = pos.pos_lnum + 1)
        then show_place pos
        else ());
        print_out pos lexbuf}
| eof  { () }
| _ as c    {out_char c lexbuf pos; print_out pos lexbuf}
