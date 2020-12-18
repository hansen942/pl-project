%{
  open Printf
  open Lexing
  open List
  open Definitions
%}

%token <string * Lexing.position> VAR TNAME TVAR
%token <int * Lexing.position> INT
%token <Lexing.position> LET EQUALS IN REC NEWTYPE PLUS MINUS LESS GREATER DIV LAMBDA ARROW LPAREN RPAREN DOT COLON LBRACE RBRACE IF THEN ELSE TRUE FALSE AND OR NOT UNIT MOD MATCH WITH BAR PROJ COMMA STAR COMMENTSTART COMMENTEND
%token EOF 

%type <Definitions.from_parser_expr> prog
%type <Definitions.annotation> t
%type <(Definitions.user_var_name * Definitions.from_parser_expr) list> cases 

%start prog

%%
prog: exp EOF                           { $1 }

exp:
    | LET VAR arglist EQUALS exp IN exp { FPLet(Name (fst $2), None, fold_right (fun x acc -> FPLambda(acc,Name (fst x),None,$1)) $3 $5, $7, $1) }
    | LAMBDA VAR COLON t DOT exp       { FPLambda($6,Name (fst $2),Some($4),$1) }
    | LAMBDA VAR DOT exp               { FPLambda($4,Name (fst $2), None,$1) }
    | NEWTYPE VAR tvararglist EQUALS sumdef IN exp { FPNewSum(fst $2,$3,$5,$7,$1) }
    | IF exp THEN exp ELSE exp          { FPIf($2,$4,$6,$1) }
    | mexp                              { $1 }
    | PROJ INT INT exp                  { FPProj($4,fst $3,fst $2,$1) }
    | LPAREN exp RPAREN                 { $2 }
    | app                               { $1}
    | sum                               { $1 }
    | binop                             { $1 }

sumdef:
    | TNAME t                             { [(fst $1,$2,snd $1)] }
    | TNAME t BAR sumdef                  { (fst $1,$2, snd $1)::$4 }
    | BAR TNAME t BAR sumdef              { (fst $2,$3, snd $2)::$5 }
    | BAR TNAME t                         { [(fst $2,$3, snd $2)] }

binop:
    | exp PLUS exp                      { FPBinop ($1,Plus,$3,$2) }
    | exp STAR exp                      { FPBinop ($1,Times,$3,$2) }
    | exp EQUALS exp                    { FPBinop ($1,Eq,$3,$2) }
    | exp MOD exp                    { FPBinop ($1,Mod,$3,$2) }
    | exp OR exp                    { FPBinop ($1,Or,$3,$2) }
    | exp AND exp                    { FPBinop ($1,And,$3,$2) }
    | exp DIV exp                    { FPBinop ($1,Div,$3,$2) }
    | exp GREATER exp                    { FPBinop ($1,G,$3,$2) }
    | exp LESS exp                    { FPBinop ($1,L,$3,$2) }

tvararglist:
    |                                  { [] }
    | TVAR                             { [fst $1] }
    | TVAR tvararglist                 { (fst $1)::$2 }

sum:
    | TNAME                             { FPSum(fst $1,FPUnit(snd $1),snd $1) }
    | TNAME app                         { FPSum(fst $1,$2,snd $1) }

app:
    | value                             { $1 }
    | app value                         { FPApplication($1,$2,(loc_of_expr $1)) }

value:
    | tuple                             { $1 }
    | UNIT                              { FPUnit($1) }
    | LPAREN MINUS exp RPAREN           { FPNeg($3,$1) }
    | INT                               { FPInt(fst $1, snd $1) }
    | TRUE                              { FPBool(true,$1) }
    | FALSE                             { FPBool(false,$1) }
    | VAR                               { FPVar(Name (fst $1), (snd $1)) }
    | LPAREN exp RPAREN                 { $2 }

arglist:
    |                                   { [] }
    | VAR                               { [$1] }
    | VAR arglist                       { $1::$2 }

tuple:
    LPAREN exp tuple_cont               {FPProd($2::$3,$1) }

tuple_cont:
    | RPAREN { [] }
    | COMMA exp tuple_cont              { $2::$3}

mexp: 
    MATCH exp WITH cases              { FPMatch($2, $4,$1) }

cases:
    |  case                              { [$1] }
    | case BAR cases                { $1::$3 }
    |  BAR cases                    { $2 }

case:
    TNAME VAR ARROW exp      { (fst $1,FPLambda($4,Name (fst $2),None,snd $1)) }

t:
| base_t                                { $1 }
| base_t ARROW t                        { AFun($1,$3,loc_of_type $1) }
| sum_w_args                            { $1 } 

sum_w_args:
| VAR targlist                          { ASumType(fst $1,$2, snd $1) }

targlist:
  | base_t                              { [$1] }
  | base_t targlist                     { $1::$2 }

base_t:
| prod                                    { $1 }
| extra_base_t                            { $1 }

extra_base_t:
   | LPAREN t RPAREN                         { $2 }
   | VAR                                     { match fst $1 with
					| "int" -> AInteger (snd $1)
					| "bool" -> ABoolean (snd $1)
					| "unit" -> AUnitType (snd $1)
					| _ -> ASumType(fst $1,[],snd $1)}
   | TVAR                                  { ATypeVar(Name (fst $1),snd $1) }


prod:
   | extra_base_t prod_cont                     { AProduct ($1::$2,loc_of_type $1) } 
prod_cont:
   | STAR extra_base_t                          { [$2] }
   | STAR extra_base_t prod_cont                { $2::$3 } 
