{
open Parser
open Printf
exception Eof
exception Err
let num_in = ref 0
}

let digit = ['0'-'9']
let int_pattern = digit+
let float_pattern = digit+['.']digit*
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
| "("              { LPAREN(lexbuf.Lexing.lex_curr_p)}
| ")"              { RPAREN(lexbuf.Lexing.lex_curr_p) }
| "."              { DOT(lexbuf.Lexing.lex_curr_p) }
| ":"              { COLON(lexbuf.Lexing.lex_curr_p) }
| "->"             { ARROW(lexbuf.Lexing.lex_curr_p) }
| "lambda"         { LAMBDA(lexbuf.Lexing.lex_curr_p) }
| "let"            { LET(lexbuf.Lexing.lex_curr_p) }
| "rec"            { REC(lexbuf.Lexing.lex_curr_p) }
| "="              { EQUALS(lexbuf.Lexing.lex_curr_p) }
| "in"             { IN(lexbuf.Lexing.lex_curr_p) }
| "+"              { PLUS(lexbuf.Lexing.lex_curr_p) }
| "-"              { MINUS(lexbuf.Lexing.lex_curr_p) }
| "%"              { MOD(lexbuf.Lexing.lex_curr_p) }
| "or"             { OR(lexbuf.Lexing.lex_curr_p) }
| "and"            { AND(lexbuf.Lexing.lex_curr_p) }
(* starts a comment *)
| "{--"            { num_in := 1; comment lexbuf }
| "<"              { LESS(lexbuf.Lexing.lex_curr_p) }
| ">"              { GREATER(lexbuf.Lexing.lex_curr_p) }
| ","              { COMMA(lexbuf.Lexing.lex_curr_p)}
| "/"              { DIV(lexbuf.Lexing.lex_curr_p) }
| "*"              { STAR(lexbuf.Lexing.lex_curr_p) }
| "true"           { TRUE(lexbuf.Lexing.lex_curr_p) }
| "false"          { FALSE(lexbuf.Lexing.lex_curr_p) }
| "if"             { IF(lexbuf.Lexing.lex_curr_p) }
| "then"           { THEN(lexbuf.Lexing.lex_curr_p) }
| "else"           { ELSE(lexbuf.Lexing.lex_curr_p) }
| "and"            { AND(lexbuf.Lexing.lex_curr_p) }
| "or"             { OR(lexbuf.Lexing.lex_curr_p) }
| "not"            { NOT(lexbuf.Lexing.lex_curr_p) }
| "match"          { MATCH(lexbuf.Lexing.lex_curr_p) }
| "with"           { WITH(lexbuf.Lexing.lex_curr_p) }
| "proj"           { PROJ(lexbuf.Lexing.lex_curr_p) }
| "newtype"        { NEWTYPE(lexbuf.Lexing.lex_curr_p) }
| "|"              { BAR(lexbuf.Lexing.lex_curr_p) }
| "()"             { UNIT(lexbuf.Lexing.lex_curr_p) }
| "unimplemented"  { STUB(lexbuf.Lexing.lex_curr_p) }
| tvarid as v      { TVAR(v,(lexbuf.Lexing.lex_curr_p)) }
| id as v          { VAR(v,(lexbuf.Lexing.lex_curr_p)) }
| bigid as i       { TNAME(i,(lexbuf.Lexing.lex_curr_p)) }
| int_pattern as n { INT(int_of_string n,(lexbuf.Lexing.lex_curr_p)) }
| float_pattern as n { FLOAT(float_of_string n,(lexbuf.Lexing.lex_curr_p)) } 
| eof              { EOF }

| _ as c  {
            let pos = lexbuf.Lexing.lex_curr_p in
            printf "Error at line %d\n" pos.Lexing.pos_lnum;
            printf "Unrecognized character: [%c]\n" c;
            exit 1
          }

