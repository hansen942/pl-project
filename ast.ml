type info = (int * int) * (int * int)

type dbvar = int
type var = string
type typename = string

type base_type =
| Int of int
| Bool of bool
| Str of string

(* Start by making a type-checker for a simple de Bruijn lambda calculus*)


(* These are our types *)
type typeexpr =
| Base of base_type
| Variable 
| Fun of (typeexpr * typeexpr) * info

type dblambda =
| Var of dbvar * typename
| Let of dblambda * dblambda
| Lambda of typename * (dblambda * typename)
| Application of dblambda * dblambda

(*
type slambda =
| Var of var * typename 
| Lambda of typename * (expr * typename) * info
| Let of var * (expr * typename) * (expr * typename) * info
| Match of slambda * (slambda list) * typename * info (*not sure about this type yet*)
| Typedef of (typename * typeexpr) * expr * info

(* this is an applied, typed lambda calculus with de Bruijn notation *)
and type dblambda =
| Var of dbvar * typename 
| Lambda of typename * (expr * typename) * info
| Let of var * (expr * typename) * (expr * typename) * info
| Typedef of (typename * typeexpr) * expr * info


type typeexpr =
| Integer
| String
| Boolean
| Sum of (typexpr list) * info
| Prod of (typexpr list) * info
| Fun of (typeexpr * typeexpr) * info

type expr = 
| Base of base_type
| Lambda of dblambda

type printable =
PInt int
| PBool bool
| PString string
*)

type prog = expr
