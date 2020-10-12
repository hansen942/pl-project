%{
open Ast
open Printf
open Lexing

let merge (fn,pos1,_) (_,_,pos2) = (fn,pos1,pos2)
%}

%token <Ast.info * int> INT
%token <Ast.info * string> VAR
%token <Ast.info> PLUS MINUS TIMES
  LPAREN RPAREN TRUE FALSE
  EQUALS NOTEQUALS LESS LESSEQ GREATER GREATEREQ
  NOT AND OR
  SKIP ASSIGN SEMI IF THEN ELSE WHILE DO
  LBRACE RBRACE
  BREAK CONTINUE TEST INPUT PRINT
  LAMBDA ARROW
%token EOF

%type <Ast.aexp> a
%type <Ast.bexp> b
%type <Ast.com> c
%type <Ast.com> p

%start p

%%

/* Expressions */

lambda : LAMBDA x ARROW e

expr   : LET VAR IN expr

