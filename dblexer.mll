%{ open Dbast
open Printf
open Lexing

%}

%token <Dbast.info * int> INT 
%token <Dbast.info * int * t> VAR
%token <Dbast.info> LAMBDA LPAREN RPAREN 


