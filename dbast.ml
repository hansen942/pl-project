open Printf
exception TypeError

type var = int 

type t =
| Integer
| NotRefd
| Fun of t * t

type dblambda =
| Int of int
| Var of var * t
| Lambda of dblambda * t
| Application of dblambda * dblambda

type config = knowntypes * dblambda

let rec shift c i dblambda =
match dblambda with
| Int n -> Int n
| Var (n,t) -> if n < c then Var (n,t) else Var(n + i,t)
| Lambda (e,t) -> Lambda (shift (c+1) i e, t)
| Application (l1, l2) -> let s = shift c i in Application (s l1, s l2)

let rec sub e1 e2 m =
match e1 with
| Int n -> Int n
| Var (v,t) -> if m = v then e2 else Var (v,t)
| Lambda (e,t) -> Lambda (sub e (shift 0 1 e2) (m+1), t)
| Application (l1, l2) -> Application ((sub l1 e2 m),(sub l2 e2 m))

let rec eval (expr:dblambda) : dblambda =
  match expr with
  | Int n -> Int n
  | Var (v,t) -> Var (v,t)
  | Lambda (e,t) -> Lambda (e,t)
  | Application (e1, e2) ->
    match e1 with
    | Lambda (e,t) -> shift 0 (-1) (sub e (shift 0 1 e2) 0)
    | _ -> raise TypeError

let rec tcheck (expr:dblambda) : t =
  match expr with
  | Int n -> Integer
  | Var (v,t) -> t
  | Lambda (e,t) -> Fun (tfind 0 e, tcheck e)
  | Application (Lambda (e1,t), l2) -> tcheck l2
  | _ -> raise TypeError
(* If we have a lambda we need to find the type of its arg *)
and tfind v e : t =
  match e with
  | Int n -> NotRefd
  | Var (v',t') -> if v = v' then t' else NotRefd
  | Lambda e -> tfind (v+1) e
  | Application (l1, l2) ->
    (* Here we need to catch the type error where v is of different types in each of these lambdas *)
    let t1 = tfind v l1 in
    let t2 = tfind v l2 in
    match t1 with
    | NotRefd -> t2
    | t1 ->
      (match t2 with
      | NotRefd -> NotRefd
      | t2 -> if t1 = t2 then t1 else raise TypeError
      )



let example = Application (Lambda (Var(0,Integer), Integer), Int 0)

(*printf (eval example);*)


