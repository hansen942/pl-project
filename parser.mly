%{
  open Printf
  open Lexing
  open List
  open Definitions
%}

%token <string> VAR TNAME TVAR
%token LPAREN RPAREN DOT COLON EOF LBRACE RBRACE
%token LAMBDA ARROW
%token <int> LET
%token EQUALS IN REC NEWTYPE
%token <int> INT
%token PLUS MINUS LESS GREATER DIV
%token IF THEN ELSE TRUE FALSE AND OR NOT UNIT MOD
%token MATCH WITH BAR PROJ
%token COMMA STAR
%token COMMENTSTART COMMENTEND

%type <Definitions.opt_t_expr> prog
%type <(Definitions.user_var_name * Definitions.opt_t_expr) list> cases 

%start prog

%%
prog: exp EOF                           { $1 }

exp:
    | LET VAR arglist EQUALS exp IN exp { OLet(Name $2, None, fold_right (fun x acc -> OLambda(acc,Name x,None)) $3 $5, $7) }
    | LET VAR arglist COLON t EQUALS exp IN exp { OLet(Name $2, Some($5), fold_right (fun x acc -> OLambda(acc,Name x,None)) $3 $7, $9) }
    | LET REC VAR arglist EQUALS exp IN exp { OLetRec(Name $3, None, fold_right (fun x acc -> OLambda(acc,Name x,None)) $4 $6, $8) }
    | LET REC VAR arglist COLON t EQUALS exp IN exp { OLetRec(Name $3, Some($6), fold_right (fun x acc -> OLambda(acc,Name x,None)) $4 $8, $10) }
    | LAMBDA VAR COLON t DOT exp       { OLambda($6,Name $2,Some($4)) }
    | LAMBDA VAR DOT exp               { OLambda($4,Name $2, None) }
    | NEWTYPE VAR tvararglist EQUALS sumdef IN exp { ONewSum($2,$3,$5,$7) }
    | IF exp THEN exp ELSE exp          { OIf($2,$4,$6) }
    | mexp                              { $1 }
    | PROJ INT INT exp                  { OProj($4,$3,$2) }
    | LPAREN exp RPAREN                 { $2 }
    | app                               { $1}
    | sum                               { $1 }
    | binop                             { $1 }

sumdef:
    | TNAME t                             { [($1,$2)] }
    | TNAME t BAR sumdef                  { ($1,$2)::$4 }
    | BAR TNAME t BAR sumdef              { ($2,$3)::$5 }
    | BAR TNAME t                         { [($2,$3)] }

binop:
    | exp PLUS exp                      { OBinop ($1,Plus,$3) }
    | exp STAR exp                      { OBinop ($1,Times,$3) }
    | exp EQUALS exp                    { OBinop ($1,Eq,$3) }
    | exp MOD exp                    { OBinop ($1,Mod,$3) }
    | exp OR exp                    { OBinop ($1,Or,$3) }
    | exp AND exp                    { OBinop ($1,And,$3) }
    | exp DIV exp                    { OBinop ($1,Div,$3) }
    | exp GREATER exp                    { OBinop ($1,G,$3) }
    | exp LESS exp                    { OBinop ($1,L,$3) }

tvararglist:
    |                                  { [] }
    | TVAR                             { [$1] }
    | TVAR tvararglist                 { $1::$2 }

sum:
    | TNAME                             { OSum($1,OUnit) }
    | TNAME app                         { OSum($1,$2) }

app:
    | value                             { $1 }
    | app value                         { OApplication($1,$2) }

value:
    | tuple                             { $1 }
    | UNIT                              { OUnit }
    | LPAREN MINUS exp RPAREN           { ONeg($3) }
    | INT                               { OInt($1) }
    | TRUE                              { OBool(true) }
    | FALSE                             { OBool(false) }
    | VAR                               { OVar(Name $1) }
    | LPAREN exp RPAREN                 { $2 }

arglist:
    |                                   { [] }
    | VAR                               { [$1] }
    | VAR arglist                       { $1::$2 }

tuple:
    LPAREN exp tuple_cont               {OProd($2::$3) }

tuple_cont:
    | RPAREN { [] }
    | COMMA exp tuple_cont              { $2::$3}

mexp: 
    MATCH exp WITH cases              { OMatch($2, $4) }

cases:
    |  case                              { [$1] }
    | case BAR cases                { $1::$3 }
    |  BAR cases                    { $2 }

case:
    TNAME VAR ARROW exp      { ($1,OLambda($4,Name $2,None)) }

t:
| base_t                                { $1 }
| base_t ARROW t                        { Fun($1,$3) }
| sum_w_args                            { $1 } 

sum_w_args:
| VAR targlist                          { SumType($1,$2) }

targlist:
  | base_t                              { [$1] }
  | base_t targlist                     { $1::$2 }

base_t:
| prod                                    { Product $1 }
| extra_base_t                            { $1 }

extra_base_t:
   | LPAREN t RPAREN                         { $2 }
   | VAR                                     { match $1 with
					| "int" -> Integer
					| "bool" -> Boolean
					| "unit" -> UnitType
					| _ -> SumType($1,[])}
   | TVAR                                  { TypeVar(Name $1) }


prod:
   | extra_base_t prod_cont                     { $1::$2 } 
prod_cont:
   | STAR extra_base_t                          { [$2] }
   | STAR extra_base_t prod_cont                { $2::$3 } 
