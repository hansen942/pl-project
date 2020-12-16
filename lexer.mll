{
open Parser
open Printf
exception Eof
exception Err
let num_in = ref 0
}

let digit = ['0'-'9']
let int_pattern = digit+
let id = ['a'-'z'] ['a'-'z' '_' '0'-'9']* ['\'']*
let bigid = ['A'-'Z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']* ['\'']*
let ws = [' ' '\t']
let tvarid = [ '\'' ] id

rule comment = parse
| "--}"            { num_in := !num_in - 1; if !num_in = 0 then token lexbuf else comment lexbuf }
| eof              { printf "hit eof in the middle of a comment"; exit 1 }
| '\n'             { Lexing.new_line lexbuf; comment lexbuf }
| _                { comment lexbuf }
and token = parse
| ws               { token lexbuf }
| '\n'             { Lexing.new_line lexbuf; token lexbuf }
| "("              { LPAREN }
| ")"              { RPAREN }
| "."              { DOT }
| ":"              { COLON }
| "->"             { ARROW }
| "lambda"         { LAMBDA }
| "let"            { LET(lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum) }
| "rec"            { REC }
| "="              { EQUALS }
| "in"             { IN }
| "+"              { PLUS }
| "-"              { MINUS }
| "%"              { MOD }
| "or"             { OR }
| "and"            { AND }
(* starts a comment *)
| "{--"            { num_in := 1; comment lexbuf }
| "<"              { LESS }
| ">"              { GREATER }
| ","              { COMMA}
| "/"              { DIV }
| "*"              { STAR }
| "true"           { TRUE }
| "false"          { FALSE }
| "if"             { IF }
| "then"           { THEN }
| "else"           { ELSE }
| "and"            { AND }
| "or"             { OR }
| "not"            { NOT }
| "match"          { MATCH }
| "with"           { WITH }
| "proj"           { PROJ }
| "newtype"        { NEWTYPE }
| "|"              { BAR }
| "()"             { UNIT }
| tvarid as v      { TVAR(v) }
| id as v          { VAR(v) }
| bigid as i       { TNAME(i) }
| int_pattern as n { INT(int_of_string n) }
| eof              { EOF }

| _ as c  {
            let pos = lexbuf.Lexing.lex_curr_p in
            printf "Error at line %d\n" pos.Lexing.pos_lnum;
            printf "Unrecognized character: [%c]\n" c;
            exit 1
          }

