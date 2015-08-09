
#r "../packages/FSharp.Compiler.Service.1.3.1.0/lib/net45/FSharp.Compiler.Service.dll"
#r "../packages/QuotationCompiler.0.0.7-alpha/lib/net45/QuotationCompiler.dll"


open QuotationCompiler

open System
open Microsoft.FSharp.Quotations

// helper functions

// <@ fun x -> (% <@ x @> ) @> ~ lambda (fun x -> x)
let lambda (f : Expr<'T> -> Expr<'R>) : Expr<'T -> 'R> =
    let var = new Var("__temp__", typeof<'T>)
    Expr.Cast<_>(Expr.Lambda(var,  f (Expr.Cast<_>(Expr.Var var))))
    
// <@ fun x y -> (% <@ x @> ... <@ y @> ) @> ~ lambda (fun x y -> x ... y )
let lambda2 (f : Expr<'T> -> Expr<'S> -> Expr<'R>) : Expr<'T -> 'S -> 'R> =
    let var = new Var("__temp__", typeof<'T>)
    let var' = new Var("__temp'__", typeof<'S>)
    Expr.Cast<_>(Expr.Lambda(var, Expr.Lambda(var',  f (Expr.Cast<_>(Expr.Var var)) (Expr.Cast<_>(Expr.Var var')))))


// A Staged Program = A Conventional Program + Staging Annotations

// val power : int -> int -> int
let rec power n x = 
    match n with 
    | 0 -> 1  | n -> x * power (n - 1) x  

// val power : int -> int code -> int code
// let rec power n x =
//     match n with
//     | 0 -> .<1>. | n -> .<.~x * .~(power (n-1) x)>.

// let power2 = .! .<fun x -> .~(power 2 .<x>.)>.

// val power' : int -> Expr<int> -> Expr<int>
let rec power' n x = 
    match n with 
    | 0 -> <@ 1 @> | n -> <@ %x * (% power' (n - 1) x ) @> 

let power2 = QuotationCompiler.Eval <| lambda (fun x -> power' 2 x)
let power2' = QuotationCompiler.Eval <| 
                <@ fun x -> (% lambda (fun x -> power' 2 x) ) x @>

power2 10 // 100
power2' 10 // 100


// A staged interpreter is a translator


type exp =  Int of int | Var of string | App of string * exp
            | Add of exp * exp | Sub of exp * exp
            | Mul of exp * exp | Div of exp * exp | Ifz of exp * exp * exp
type def = Declaration of string * string * exp
type prog = Program of def list * exp

// factorial
let fact10Program = 
    Program ([Declaration
                ("fact","x", Ifz (Var "x", Int 1,
                                    Mul (Var"x", (App ("fact", Sub (Var "x", Int 1))))))],
                App ("fact", Int 10))


exception Yikes
(* env0, fenv : ’a -> ’b *)
let env0 = fun x -> raise Yikes
let fenv0 = env0 
(* ext : (’a -> ’b) -> ’a -> ’b -> ’a -> ’b *)
let ext env x v = fun y -> if x = y then v else env y

// val eval1 : exp -> (string -> int) -> (string -> int -> int) -> int 
let rec eval1 e env fenv =
    match e with
    Int i -> i
    | Var s -> env s
    | App (s, e2) -> (fenv s) (eval1 e2 env fenv)
    | Add (e1, e2) -> (eval1 e1 env fenv) + (eval1 e2 env fenv)
    | Sub (e1, e2) -> (eval1 e1 env fenv) - (eval1 e2 env fenv)
    | Mul (e1, e2) -> (eval1 e1 env fenv) * (eval1 e2 env fenv)
    | Div (e1, e2) -> (eval1 e1 env fenv) / (eval1 e2 env fenv)
    | Ifz (e1, e2, e3) -> if (eval1 e1 env fenv) = 0 then (eval1 e2 env fenv)
                          else (eval1 e3 env fenv)


// val peval1 : prog -> (string -> int) -> (string -> int -> int) -> int 
let rec peval1 p env fenv =
    match p with
    | Program ([], e) -> eval1 e env fenv
    | Program (Declaration (s1, s2, e1) :: tl, e) ->
        let rec f x = eval1 e1 (ext env s2 x) (ext fenv s1 f)
        peval1 (Program (tl, e)) env (ext fenv s1 f)

peval1 fact10Program env0 fenv0 // 3628800



// val eval2 : exp -> (string -> Expr<int>) -> (string -> Expr<int -> int>) -> Expr<int> 
let rec eval2 e env fenv =
    match e with
    | Int i -> <@ i @>
    | Var s -> env s
    | App (s, e2) -> <@ (% fenv s ) (% eval2 e2 env fenv ) @>
    | Add (e1, e2) -> <@ (% eval2 e1 env fenv ) + (% eval2 e2 env fenv ) @>
    | Sub (e1, e2)-> <@ (% eval2 e1 env fenv ) - (% eval2 e2 env fenv ) @>
    | Mul (e1, e2)-> <@ (% eval2 e1 env fenv ) * (% eval2 e2 env fenv ) @>
    | Div (e1, e2)-> <@ (% eval2 e1 env fenv ) / (% eval2 e2 env fenv ) @>
    | Ifz (e1, e2, e3) -> <@ if (% eval2 e1 env fenv ) = 0
                           then (% eval2 e2 env fenv )
                           else (% eval2 e3 env fenv ) @>

// val peval2 : prog -> (string -> Expr<int>) -> (string -> Expr<int -> int>) -> Expr<int> 
let rec peval2 p env fenv=
    match p with
    | Program ([], e) -> eval2 e env fenv
    | Program (Declaration (s1, s2, e1) :: tl, e) ->
        <@  let rec f x = (% lambda2 (fun f x -> eval2 e1 (ext env s2 x) (ext fenv s1 f))) f x
            in (% lambda (fun f -> peval2 (Program(tl, e)) env (ext fenv s1 f)) ) f @>

let fact10 = peval2 fact10Program env0 fenv0

QuotationCompiler.Eval fact10 // 3628800