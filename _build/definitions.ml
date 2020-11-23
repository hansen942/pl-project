open List
(** This file contains all the shared types that the other modules need and also some functions that allow these types to be displayed.*)

(** users write programs where identifiers are strings *)
type user_var_name = string

(** [var_name] can use integers because this makes getting new variable names easier *)
type var_name =
| Sub of int
| Name of user_var_name 

type binop =
| Plus
| Times
| Subtract
| Mod
| L
| G
| And
| Or
| Eq
| Div

(** [expr] is the type of our untyped expressions. It is essentially the applied lambda calculus. *)
type expr =
| Int of int
| Var of var_name
| Lambda of expr * var_name
| Application of expr * expr
| If of expr * expr * expr
| Bool of bool
| Unit
| Print of expr
| Sum of user_var_name * expr (* var_name is the constructor name used *)
| Prod of expr list
| Match of expr * ((user_var_name * expr) list)
| Proj of expr * int
| Neg of expr
| Binop of expr * binop * expr
(*| Lazy of expr ref*)

(*module Compare_VName : Map.OrderedType = struct
type t = var_name
let compare = compare 
end*)
(** [sugar] is supposed to represent syntactic sugar over the base language, however, sugar is somehwat a misnomer.
  This is because a properly typed program cannot contain [Z], the Z combinator, however during desugaring we introduce [Z] in the untyped base language when dealing with [LetRec] expressions.
  Dealing with the recursion in two different ways allows programs to type check even though they will be desugared to an untypeable program.
 It is worth noting here that let rec will act recursively on ALL expressions, not just functions, so that [let x = 1 in let rec x = x+1 in x] will not terminate, but [let x = 1 in let x = x+1 in x] will terminate and have value [2].
  *)
type sugar = 
| LetRec of var_name * sugar * sugar 
| Let of var_name * sugar * sugar 
| Z
| SInt of int
| SVar of var_name
| SLambda of sugar * var_name
| SApplication of sugar * sugar
| SIf of sugar * sugar * sugar
| SBool of bool
| STimes of sugar * sugar
| SEq of sugar * sugar
| SUnit
| SPrint of sugar
| SSum of user_var_name * sugar (* var_name is the constructor name used *)
| SProd of sugar list
| SMatch of sugar * ((user_var_name * sugar) list)
| SProj of sugar * int
| SNeg of sugar 
| SBinop of sugar * binop * sugar

(** [z] is the Z-combinator *)
let z =
  let innermost = Lambda ( Application (Application (Var (Name "x"), Var (Name "x")), Var (Name "y")) , Name "y") in
  let lazy_omega' = Lambda (Application(Var (Name "f"), innermost), Name "x") in
  Lambda (Application (lazy_omega', lazy_omega'), Name "f") 

let rec desugar : sugar -> expr = function
| LetRec (v,e1,e2) -> Application (Lambda (desugar e2,v), Application(desugar Z, Lambda (desugar e1,v)))
| Let (v,e1,e2) -> Application (Lambda (desugar e2,v), desugar e1)
| Z -> z
| SInt n -> Int n
| SVar v -> Var v
| SLambda(e,x) -> Lambda(desugar e,x)
| SApplication(e1,e2) -> Application(desugar e1,desugar e2)
| SIf(e1,e2,e3) -> If(desugar e1,desugar e2,desugar e3)
| SBool b -> Bool b
| SUnit -> Unit
| SPrint e -> Print (desugar e)
| SSum(n,e) -> Sum(n,desugar e) 
| SProd elist -> Prod(map desugar elist)
| SMatch (e,cases) -> Match(desugar e, map (fun (x,y) -> (x,desugar y)) cases)
| SProj(e,n) -> Proj(desugar e,n)
| SNeg e -> Neg (desugar e)
| SBinop (e1,binop,e2) -> Binop(desugar e1,binop, desugar e2)


let rec is_val = function
| Int _ -> true
| Bool _ -> true
| Lambda _ -> true
| Unit -> true
| Prod elist -> for_all is_val elist
| Sum (name,e) -> is_val e
| _ -> false

let rec naive_list_union' acc l1 = function
| h::t -> if mem h l1 then naive_list_union' acc l1 t else naive_list_union' (h::acc) l1 t
| [] -> acc @ l1

(** [list_union l1 l2] is a list that contains all the elements of [l1] and [l2] with no repeats, assuming that [l1] and [l2] also contain no repeats.
    Also note this is not tail recursive (because of use of [@] operator) and will have recursion depth = length of [l2]*)
let naive_list_union : 'a list -> 'a list -> 'a list = naive_list_union' []

(** [fv e] gives a list containing all the free variables of [e].
    Ideally, we would replace the list with a set but this requires defining an order on expressions so I'm just building it with lists first.
   if a projection will fail then it doesn't have any free variables*)
let rec fv : expr -> var_name list = function
| Int _ -> []
| Var v -> [v]
| Lambda (ebody,arg) -> filter (fun x -> not (x = arg)) (fv ebody)
| Application (e1,e2) -> naive_list_union (fv e1) (fv e2)
| If (e1,e2,e3) -> naive_list_union (fv e1) (naive_list_union (fv e2) (fv e3))
| Bool _ -> []
| Unit -> []
| Print e -> fv e
| Sum (name,e) -> fv e
| Prod elist -> fold_left (fun acc x -> naive_list_union acc (fv x)) [] elist
| Match (e,functions) ->
  naive_list_union (fv e) (fold_left (fun acc x -> naive_list_union acc (fv (snd x))) [] functions)
| Proj (expr,n) ->(
  match expr with
  | Prod elist -> (match nth_opt elist n with None -> [] | Some e -> fv e )
  | _ -> []
  )
| Neg e -> fv e
| Binop (e1,binop,e2) -> naive_list_union (fv e1) (fv e2)


let string_of_var v : string =
match v with
| Sub x -> Printf.sprintf "ⓥ %n" x
| Name v -> v

let string_of_binop : binop -> string = function
| Eq -> "="
| Subtract -> "-"
| Plus -> "+"
| Mod -> "%"
| Times -> "*"
| L -> "<"
| G -> ">"
| And -> "and"
| Or -> "or"
| Div -> "/"

let rec string_of_expr : expr -> string = function
| Int n -> string_of_int n
| Var v -> string_of_var v
| Bool b -> string_of_bool b
| Lambda (e,arg) -> Printf.sprintf "λ%s.%s" (string_of_var arg) (string_of_expr e) 
| Application (e1,e2) -> Printf.sprintf "(%s) (%s)" (string_of_expr e1) (string_of_expr e2)
| If (e1,e2,e3) -> Printf.sprintf "if %s then %s else %s" (string_of_expr e1) (string_of_expr e2) (string_of_expr e3)
| Unit -> "()"
| Print e -> Printf.sprintf "print %s" (string_of_expr e)
| Sum (name,e) -> Printf.sprintf "%s %s" name (string_of_expr e)
| Prod elist ->(
  match elist with
  | [] -> "()"
  | h::t -> let body = (string_of_expr h) ^ (fold_left (fun acc x -> acc ^ ", " ^ (string_of_expr x)) "" t) in
  Printf.sprintf "(%s)" body
  )
| Match (e,cases) ->
  let body = fold_left (fun acc x -> acc ^ "| " ^ (fst x) ^ " -> " ^ (string_of_expr (snd x))) "" cases in
  Printf.sprintf "match %s with %s" (string_of_expr e) body
| Proj (e,n) -> Printf.sprintf "%s[%s]" (string_of_expr e) (string_of_int n)
| Neg e -> Printf.sprintf "(-%s)" (string_of_expr e) 
| Binop (e1,binop,e2) -> Printf.sprintf "%s %s %s" (string_of_expr e1) (string_of_binop binop) (string_of_expr e2)

let rec string_of_sugar : sugar -> string = function
| Let (v,e1,e2) -> Printf.sprintf "let %s = %s in %s" (string_of_var v) (string_of_sugar e1) (string_of_sugar e2)
| LetRec (v,e1,e2) -> Printf.sprintf "let rec %s = %s in %s" (string_of_var v) (string_of_sugar e1) (string_of_sugar e2)
| Z -> "Z"
| SInt n -> string_of_int n
| SVar v -> string_of_var v
| SBool b -> string_of_bool b
| SLambda (e,arg) -> Printf.sprintf "λ%s.%s" (string_of_var arg) (string_of_sugar e) 
| SApplication (e1,e2) -> Printf.sprintf "(%s) (%s)" (string_of_sugar e1) (string_of_sugar e2)
| SIf (e1,e2,e3) -> Printf.sprintf "if %s then %s else %s" (string_of_sugar e1) (string_of_sugar e2) (string_of_sugar e3)
| SUnit -> "()"
| SPrint e -> Printf.sprintf "print %s" (string_of_sugar e)
| SSum (name,e) -> Printf.sprintf "%s %s" name (string_of_sugar e)
| SProd elist ->(
  match elist with
  | [] -> "()"
  | h::t -> let body = (string_of_sugar h) ^ (fold_left (fun acc x -> acc ^ ", " ^ (string_of_sugar x)) "" t) in
  Printf.sprintf "(%s)" body
  )
| SMatch (e,cases) ->
  let body = fold_left (fun acc x -> acc ^ "| " ^ (fst x) ^ " -> " ^ (string_of_sugar (snd x))) "" cases in
  Printf.sprintf "match %s with %s" (string_of_sugar e) body
| SProj (e,n) -> Printf.sprintf "%s[%s]" (string_of_sugar e) (string_of_int n)
| SNeg e -> Printf.sprintf "(-%s)" (string_of_sugar e) 
| SBinop (e1,binop,e2) -> Printf.sprintf "%s %s %s" (string_of_sugar e1) (string_of_binop binop) (string_of_sugar e2)

(** [type_class] serves the purpose of telling what generic types can have generic operations done on them *)
(* TODO: allow way to construct new type classes, and change this type to include user-defined type classes *)
type type_class =
| Printable

let string_of_typeclass = function
| Printable -> "printable"

type class_constraints = type_class list

(** [expr_type] is the type of types in our language. Hopefully we will extend this to include user-defined types as well.*)
type expr_type =
| Integer
| Boolean
| Fun of expr_type * expr_type
| UnitType
| TypeVar of var_name
| Product of expr_type list
| SumType of user_var_name * (expr_type list) (* only put type name and parametric types because will not be known until later. Constructors but into a context *) 

let rec ftv = function
| Fun (t1,t2) ->
  let ft1v = ftv t1 in 
  let ft2v = ftv t2 in
  naive_list_union ft1v ft2v
| Integer -> []
| Boolean -> []
| UnitType -> []
| TypeVar v -> [v]
| Product tlist -> fold_left (fun acc x -> naive_list_union acc (ftv x)) [] tlist
| SumType (name,args) -> fold_left (fun acc x -> naive_list_union acc (ftv x)) [] args

let rec tsub t_new tvar = fun t ->
  match t with
  | TypeVar v -> if v = tvar then t_new else t
  | Fun (t1,t2) ->
    Fun (tsub t_new tvar t1, tsub t_new tvar t2)
  | Product tlist -> Product (map (tsub t_new tvar) tlist)
  | SumType (name,args) -> SumType (name,(map (tsub t_new tvar) args))
  | _ -> t

let rec string_of_type = function
| Integer -> "int"
| Boolean -> "bool"
| Fun (t1,t2) ->
  let s1 =
    match t1 with
    | Fun _ -> Printf.sprintf "(%s)" (string_of_type t1)
    | _ -> string_of_type t1
  in
  Printf.sprintf "%s →  %s" s1 (string_of_type t2)
| UnitType -> "unit"
| SumType (name,args) ->
  (match args with
  | [] -> name
  | _ ->
  let arg_string = fold_right (fun x acc -> " " ^ (string_of_type x) ^ acc) args "" in
  name ^ arg_string) 
| Product tlist ->
  let entries = map string_of_type tlist in
  (match entries with
  | [] -> "EmptyProduct"
  | h::[] -> Printf.sprintf "unary product %s" h
  | h::t -> h ^ (fold_left (fun acc x -> acc ^ " * " ^ x) "" t)
  )
| TypeVar v -> Printf.sprintf "tvar %s" (string_of_var v)

(** [known_classes] is an association list, if [(a,[c1,c2,c3])] is in the list this means that we know [a] is in the type classes [c1,c2,c3]. *)
type known_classes = (var_name * class_constraints) list

type class_constrained_expr_type = expr_type * known_classes

let string_of_tvar_constraint v = function
  | c::[] -> Printf.sprintf "∀ %s %s." (string_of_typeclass c) (string_of_var v)
  | [] -> Printf.sprintf "∀ %s." (string_of_var v)
  | lst ->
    let cons_string = fold_left (fun acc x -> acc ^ ", " ^ string_of_typeclass x) "" lst in
    Printf.sprintf "∀ (%s) %s." cons_string (string_of_var v)

(** this gives string for the type and class constraints associated *)
let string_of_class_constrained_expr_type = function
  | (t,kc) -> let kc_needed = filter (fun x -> mem (fst x) (ftv t)) kc in
    let quantifiers = fold_left (fun acc x -> acc ^ " " ^ (string_of_tvar_constraint (fst x) (snd x))) "" kc_needed in
    Printf.sprintf "%s%s" quantifiers (string_of_type t)

(** Elements of [typed_expr] represent expressions which are annotated with types.*)
type typed_expr =
| TInt of int
| TBool of bool
| TVar of var_name
| TLambda of typed_expr * var_name * expr_type
| TApplication of typed_expr * typed_expr
| TIf of typed_expr * typed_expr * typed_expr
| TUnit
| TPrint of typed_expr
| TSum of user_var_name * typed_expr (* var_name is the constructor name used *)
| TProd of typed_expr list
| TMatch of typed_expr * ((user_var_name * typed_expr) list)
| TProj of typed_expr * int * int (* index you want, length of tuple you expect *)
| TNeg of typed_expr
| TBinop of typed_expr * binop * typed_expr
| NewSum of user_var_name * (user_var_name list) * (user_var_name * expr_type) list * typed_expr (* new type name, type variables used, constructors by types, next expression *)
| TLet of var_name * typed_expr * typed_expr
| TLetRec of var_name * expr_type * typed_expr * typed_expr


let rec string_of_typed_expr : typed_expr -> string = function
| TInt n -> string_of_int n
| TVar v -> string_of_var v
| TBool b -> string_of_bool b
| TLambda (e,arg,t) -> Printf.sprintf "λ%s : %s.%s" (string_of_var arg) (string_of_type t) (string_of_typed_expr e) 
| TApplication (e1,e2) -> Printf.sprintf "(%s) (%s)" (string_of_typed_expr e1) (string_of_typed_expr e2)
| TIf (e1,e2,e3) -> Printf.sprintf "if %s then %s else %s" (string_of_typed_expr e1) (string_of_typed_expr e2) (string_of_typed_expr e3)
| TUnit -> "()"
| TPrint e -> (Printf.sprintf "print %s" (string_of_typed_expr e))
| TSum (name,expr) -> Printf.sprintf "%s %s" name (string_of_typed_expr expr)
| TProd elist ->(
  match elist with
  | [] -> "()"
  | h::t -> let body = (string_of_typed_expr h) ^ (fold_left (fun acc x -> acc ^ ", " ^ (string_of_typed_expr x)) "" t) in
  Printf.sprintf "(%s)" body
  )
| TMatch (e,cases) ->
  let body = fold_left (fun acc x -> acc ^ "| " ^ (fst x) ^ " -> " ^ (string_of_typed_expr (snd x))) "" cases in
  Printf.sprintf "match %s with %s" (string_of_typed_expr e) body
| TProj (e,n,l) -> Printf.sprintf "proj %s %s %s" (string_of_int l) (string_of_int n) (string_of_typed_expr e) 
| NewSum (name,vars,cons,s) ->(
  let bind_vars = fold_right (fun x acc -> x ^ " " ^ acc) vars "" in
  match cons with
  | [] -> Printf.sprintf "%s = void" name
  | h::t -> let body = match h with (ch,th) -> ch ^ " " ^ (string_of_type th) ^ (fold_right (fun (c,t) acc -> (Printf.sprintf " | %s %s" c (string_of_type t)) ^ acc) t "") in
  let dec = Printf.sprintf "newtype %s %s = %s" name bind_vars body in
  Printf.sprintf "%s in %s" dec (string_of_typed_expr s)
  )
| TLet (v,e1,e2) -> Printf.sprintf "let %s = %s in %s" (string_of_var v) (string_of_typed_expr e1) (string_of_typed_expr e2)
| TLetRec (v,tv,e1,e2) -> Printf.sprintf "let rec %s : %s = %s in %s" (string_of_var v) (string_of_type tv) (string_of_typed_expr e1) (string_of_typed_expr e2)
| TNeg e -> Printf.sprintf "(-%s)" (string_of_typed_expr e) 
| TBinop (e1,binop,e2) -> Printf.sprintf "%s %s %s" (string_of_typed_expr e1) (string_of_binop binop) (string_of_typed_expr e2)

(* Note: for type variables you should check the known type class constraints to see if it is declared prinatble before calling this. *)
let rec printable : expr_type -> bool = function
| UnitType -> true
| Integer -> true
| Boolean -> true
| Fun _ -> false
| SumType (name,args) -> false
(* we also need to know the actual structure of the sumtype from the context*)
| Product tlist -> for_all printable tlist
| TypeVar _ -> false

(* these types only have optional type annotations *)
type opt_t_expr = 
| OInt of int
| OBool of bool
| OVar of var_name
| OLambda of opt_t_expr * var_name * (expr_type option)
| OApplication of opt_t_expr * opt_t_expr
| OIf of opt_t_expr * opt_t_expr * opt_t_expr
| OUnit
| OPrint of opt_t_expr
| OSum of user_var_name * opt_t_expr
| OProd of opt_t_expr list
| OMatch of opt_t_expr * ((user_var_name * opt_t_expr) list)
| OProj of opt_t_expr * int * int
| ONewSum of user_var_name * (user_var_name list) * (user_var_name * expr_type) list * opt_t_expr
| OLet of var_name * opt_t_expr * opt_t_expr 
| OLetRec of var_name * (expr_type option) * opt_t_expr * opt_t_expr 
| ONeg of opt_t_expr
| OBinop of opt_t_expr * binop * opt_t_expr

type ('a,'s) state = 's -> ('a * 's)
let return x = fun s -> (x,s)
(* this is standard bind *) 
let (>>=) (init_state:('a,'s) state) (transform:'a -> ('b,'s) state) =
  (fun old_state ->
  let first_val, first_state = init_state old_state in
  transform first_val first_state
  )
let (let*) x f = x >>= f
let state s = (s,s)
(* allows one to map stateful computations over a list; state is passed right to left *)
let state_fmap f lst =
  fold_right (fun x acc -> let* r = f x in let* acc' = acc in return(r::acc')) lst (return [])

let init_name = Sub 0
let pull_name = function
| Sub n -> (Sub n, Sub (n+1))
| _ -> failwith "internal error" 

let rec annotate_opt_t_expr oexpr =
  let f = annotate_opt_t_expr in
  match oexpr with
  | OInt n -> return(TInt n)
  | OBool b -> return(TBool b)
  | OVar v -> return(TVar v)
  | OLambda(e1,v,t_opt) ->
    let* e1' = f e1 in
    let* t =
    match t_opt with
    | Some t -> return t
    | None -> let* name = pull_name in return(TypeVar(name))
    in
    return(TLambda(e1',v,t))
  | OApplication(e1,e2) ->
    let* e1' = f e1 in
    let* e2' = f e2 in
    return(TApplication(e1',e2'))
  | OIf(e1,e2,e3) ->
    let* e1' = f e1 in
    let* e2' = f e2 in
    let* e3' = f e3 in
    return(TIf(e1',e2',e3'))
  | OPrint(e) ->
    let* e' = f e in
    return(TPrint(e'))
  | OSum(name,e) ->
    let* e' = f e in
    return(TSum(name,e'))
  | OProd(elist) ->
    let* elist' = fold_right (fun x acc -> let* x' = f x in let* acc' = acc in return(x'::acc')) elist (return []) in
    return(TProd(elist'))
  | OMatch(e,cases) ->
    let* e' = f e in
    let* cases' = fold_right (fun (cons,e) acc -> let* e' = f e in let* acc' = acc in return((cons,e')::acc')) cases (return []) in
    return(TMatch(e',cases'))
  | OProj(e,i,l) ->
    let* e' = f e in
    return(TProj(e',i,l))
  | OLet(v,e1,e2) ->
    let* e1' = f e1 in
    let* e2' = f e2 in
    return(TLet(v,e1',e2'))
  | OLetRec(v,t_opt,e1,e2) ->
    let* t =
    match t_opt with
    | None -> let* name = pull_name in return(TypeVar(name))
    | Some t -> return t
    in
    let* e1' = f e1 in
    let* e2' = f e2 in
    return(TLetRec(v,t,e1',e2'))
  | ONewSum (w,x,y,z) -> let* z' = f z in return(NewSum (w,x,y,z')) 
  | OUnit -> return TUnit
  | ONeg e -> let* e' = f e in return (TNeg e')
  | OBinop (e1,binop,e2) -> let* e1' = f e1 in let* e2' = f e2 in return(TBinop (e1',binop,e2'))
