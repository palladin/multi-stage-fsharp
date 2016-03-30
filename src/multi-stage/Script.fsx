
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

let duration f name = 
    let timer = new System.Diagnostics.Stopwatch()
    timer.Start()
    let returnValue = f()
    for i = 1 to 1000000 do
        let returnValue = f()
        ()
    printfn "Elapsed msec for %s: %i" name timer.ElapsedMilliseconds
    returnValue

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

let rec factorial n =
    match n with
    | 0 | 1 -> 1
    | _ -> n * factorial(n-1)

duration (fun() -> power2 10) "power2"// 100
duration (fun() -> power2' 10) "power2'"// 100

duration (fun () -> factorial 10) "native factorial 10"

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
    | Int i -> i
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

duration (fun() -> peval1 fact10Program env0 fenv0) "interpreted fact10Program"// 3628800

// val eval2 : exp -> (string -> Expr<int>) -> (string -> Expr<int -> int>) -> Expr<int> 
let rec eval2 e env fenv =
    match e with
    | Int i -> <@ i @>
    | Var s -> env s
    | App (s, e2) -> <@ (% fenv s ) (% eval2 e2 env fenv ) @>
    | Add (e1, e2) -> <@ (% eval2 e1 env fenv ) + (% eval2 e2 env fenv ) @>
    | Sub (e1, e2) -> <@ (% eval2 e1 env fenv ) - (% eval2 e2 env fenv ) @>
    | Mul (e1, e2) -> <@ (% eval2 e1 env fenv ) * (% eval2 e2 env fenv ) @>
    | Div (e1, e2) -> <@ (% eval2 e1 env fenv ) / (% eval2 e2 env fenv ) @>
    | Ifz (e1, e2, e3) -> <@ if (% eval2 e1 env fenv ) = 0
                             then (% eval2 e2 env fenv )
                             else (% eval2 e3 env fenv ) @>

// val peval2 : prog -> (string -> Expr<int>) -> (string -> Expr<int -> int>) -> Expr<int> 
let rec peval2 p env fenv =
    match p with
    | Program ([], e) -> eval2 e env fenv
    | Program (Declaration (s1, s2, e1) :: tl, e) ->
        <@  let rec f x = (% lambda2 (fun f x -> eval2 e1 (ext env s2 x) (ext fenv s1 f))) f x
            in (% lambda (fun f -> peval2 (Program(tl, e)) env (ext fenv s1 f)) ) f @>

let fact10 = peval2 fact10Program env0 fenv0

let compiledFact10 = QuotationCompiler.ToFunc fact10

duration (fun() -> compiledFact10 ()) "compiled fact10Program"// 3628800

// Interpreter with Error Handling

// val eval3 : exp -> (string -> int) -> (string -> int -> int option) -> int option 
let rec eval3 e env fenv =
    match e with
    | Int i -> Some i
    | Var s -> Some (env s)
    | App (s, e2) -> match (eval3 e2 env fenv) with
                     | Some x -> (fenv s) x
                     | None -> None
    | Add (e1, e2) -> match (eval3 e1 env fenv), (eval3 e2 env fenv) with
                      | Some x, Some y -> Some (x + y)
                      | _ -> None
    | Sub (e1, e2) -> match (eval3 e1 env fenv), (eval3 e2 env fenv) with
                      | Some x, Some y -> Some (x - y)
                      | _ -> None
    | Mul (e1, e2) -> match (eval3 e1 env fenv), (eval3 e2 env fenv) with
                      | Some x, Some y -> Some (x * y)
                      | _ -> None
    | Div (e1, e2) -> match (eval3 e1 env fenv), (eval3 e2 env fenv) with
                      | Some x, Some y -> 
                        if y = 0 then None else Some (x / y)
                      | _ -> None
    | Ifz (e1, e2, e3) -> match (eval3 e1 env fenv)  with 
                          | Some x -> if x = 0 then (eval3 e2 env fenv) else (eval3 e3 env fenv)
                          | None -> None


// val peval3 : prog -> (string -> int) -> (string -> int -> int option) -> int option 
let rec peval3 p env fenv =
    match p with
    | Program ([], e) -> eval3 e env fenv
    | Program (Declaration (s1, s2, e1) :: tl, e) ->
        let rec f x = eval3 e1 (ext env s2 x) (ext fenv s1 f)
        peval3 (Program (tl, e)) env (ext fenv s1 f)


let fact20Div2Program = 
    Program ([Declaration
                ("fact","x", Ifz (Var "x", Int 1,
                                    Mul (Var"x", (App ("fact", Sub (Var "x", Int 1))))))],
                App ("fact", Div (Int 20, Int 2)))
                

duration (fun() -> peval3 fact20Div2Program env0 fenv0) "interpreted fact20Div2Program w/error handling"

// Staged Interpreter with Error Handling

// val eval4 : exp -> (string -> Expr<int>) -> (string -> Expr<int -> int option>) -> Expr<int option> 
let rec eval4 e env fenv =
    match e with
    | Int i -> <@ Some i @>
    | Var s -> <@ Some (% env s ) @>
    | App (s, e2) -> <@ match (% eval4 e2 env fenv ) with
                        | Some x -> (% fenv s ) x
                        | None -> None @>
    | Add (e1, e2) -> <@ match (% eval4 e1 env fenv ), (% eval4 e2 env fenv ) with
                         | Some x, Some y -> Some (x + y)
                         | _ -> None @>
    | Sub (e1, e2) -> <@ match (% eval4 e1 env fenv ), (% eval4 e2 env fenv ) with
                         | Some x, Some y -> Some (x - y)
                         | _ -> None @>
    | Mul (e1, e2) -> <@ match (% eval4 e1 env fenv ), (% eval4 e2 env fenv ) with
                         | Some x, Some y -> Some (x * y)
                         | _ -> None @>
    | Div (e1, e2) -> <@ match (% eval4 e1 env fenv ), (% eval4 e2 env fenv ) with
                         | Some x, Some y -> 
                            if y = 0 then None else Some (x / y)
                         | _ -> None @>
    | Ifz (e1, e2, e3) -> <@ match (% eval4 e1 env fenv )  with 
                             | Some x -> if x = 0 then (% eval4 e2 env fenv ) else (% eval4 e3 env fenv )
                             | None -> None @>


// val peval4 : prog -> (string -> int) -> (string -> int -> int option) -> int option 
let rec peval4 p env fenv =
    match p with
    | Program ([], e) -> eval4 e env fenv
    | Program (Declaration (s1, s2, e1) :: tl, e) ->
        <@  let rec f x = (% lambda2 (fun f x -> eval4 e1 (ext env s2 x) (ext fenv s1 f))) f x
            in (% lambda (fun f -> peval4 (Program(tl, e)) env (ext fenv s1 f)) ) f @>

            
let Qfact20Div2 = QuotationCompiler.ToFunc (peval4 fact20Div2Program env0 fenv0)

duration (fun() -> Qfact20Div2 ()) "compiled fact20Div2Program with error handling"

// CPS Interpreter with Error Handling

// val eval5 : exp -> (string -> int) -> (string -> int -> int) -> (int option -> ’a) -> ’a 
let rec eval5 e env fenv k =
    match e with
    | Int i -> k (Some i)
    | Var s -> k (Some (env s))
    | App (s, e2) -> eval5 e2 env fenv
                      (fun r -> match r with
                                | Some x -> k (Some ((fenv s) x))
                                | None -> k None)
    | Add (e1, e2) -> eval5 e1 env fenv
                       (fun r ->
                         eval5 e2 env fenv
                           (fun s -> match (r,s) with
                                     | (Some x, Some y) -> k (Some (x + y))
                                     | _ -> k None))
    | Sub (e1, e2) -> eval5 e1 env fenv
                       (fun r ->
                         eval5 e2 env fenv
                           (fun s -> match (r,s) with
                                     | (Some x, Some y) -> k (Some (x - y))
                                     | _ -> k None)) 
    | Mul (e1, e2) -> eval5 e1 env fenv
                       (fun r ->
                         eval5 e2 env fenv
                           (fun s -> match (r,s) with
                                     | (Some x, Some y) -> k (Some (x * y))
                                     | _ -> k None)) 
    | Div (e1, e2) -> eval5 e1 env fenv
                       (fun r ->
                         eval5 e2 env fenv (fun s -> match (r,s) with
                                                     | (Some x, Some y) ->
                                                            if y=0 then k None
                                                            else k (Some (x / y))
                                                     | _ -> k None))
    | Ifz (e1, e2, e3) -> eval5 e1 env fenv
                            (fun r -> match r with
                                      | Some x -> 
                                        if x = 0 then eval5 e2 env fenv k
                                        else eval5 e3 env fenv k
                                      | None   -> k None)

// val pevalK5 : prog -> (string -> int) -> (string -> int -> int) -> (int option -> int) -> int 
let rec pevalK5 p env fenv k =
    match p with
    | Program ([], e) -> eval5 e env fenv k
    | Program (Declaration (s1, s2, e1) :: tl, e) ->
        let rec f x = eval5 e1 (ext env s2 x) (ext fenv s1 f) k
          in pevalK5 (Program(tl, e)) env (ext fenv s1 f) k

(* peval5 : prog -> (string -> int) -> (string -> int -> int) -> int *)
let peval5 p env fenv =
     pevalK5 p env fenv (function Some x -> x
                                | None -> raise <| new DivideByZeroException())

duration (fun() -> peval5 fact20Div2Program env0 fenv0 ) "interpreted CPS fact20Div2Program with error handling" // 3628800

// Staged CPS Interpreter with Error Handling

// val eval6 : exp -> (string -> Expr<int>) -> (string -> Expr<int -> int>) -> (Expr<int> option -> Expr<’a>) -> Expr<’a> 
let rec eval6 e env fenv k =
    match e with
    | Int i -> k (Some <@ i @>)
    | Var s -> k (Some (env s))
    | App (s, e2) -> eval6 e2 env fenv
                      (fun r -> match r with
                                | Some x -> k (Some <@ (% fenv s)  %x @>)
                                | None -> k None)
    | Add (e1, e2) -> eval6 e1 env fenv
                       (fun r ->
                         eval6 e2 env fenv
                           (fun s -> match (r, s) with
                                     | (Some x, Some y) -> k (Some <@ %x + %y @>)
                                     | _ -> k None))
    | Sub (e1, e2) -> eval6 e1 env fenv
                       (fun r ->
                         eval6 e2 env fenv
                           (fun s -> match (r, s) with
                                     | (Some x, Some y) -> k (Some <@ %x - %y @>)
                                     | _ -> k None)) 
    | Mul (e1, e2) -> eval6 e1 env fenv
                       (fun r ->
                         eval6 e2 env fenv
                           (fun s -> match (r, s) with
                                     | (Some x, Some y) -> k (Some <@ %x * %y @>)
                                     | _ -> k None)) 
    | Div (e1, e2) -> eval6 e1 env fenv
                       (fun r ->
                         eval6 e2 env fenv (fun s -> match (r, s) with
                                                     | (Some x, Some y) ->
                                                            <@ if %y = 0 then (% k None )
                                                               else (% k (Some <@ %x / %y @>) ) @>
                                                     | _ -> k None))
    | Ifz (e1, e2, e3) -> eval6 e1 env fenv
                            (fun r -> match r with
                                      | Some x -> 
                                        <@ if %x = 0 then (% eval6 e2 env fenv k )
                                           else (% eval6 e3 env fenv k ) @>
                                      | None   -> k None)

// val pevalK6 : prog -> (string -> Expr<int>) -> (string -> Expr<int -> int>) -> (Expr<int> option -> Expr<int>) -> Expr<int>
let rec pevalK6 p env fenv k =
    match p with
    | Program ([], e) -> eval6 e env fenv k
    | Program (Declaration (s1, s2, e1) :: tl, e) ->
        <@  let rec f x = (% lambda2 (fun f x -> eval6 e1 (ext env s2 x) (ext fenv s1 f) k)) f x
            in (% lambda (fun f -> pevalK6 (Program(tl, e)) env (ext fenv s1 f) k) ) f @>

// val peval6 : prog -> (string -> Expr<int>) -> (string -> Expr<int -> int>) -> Expr<int>
let peval6 p env fenv =
     pevalK6 p env fenv (function Some x -> x
                                | None -> <@ raise <| new DivideByZeroException() @>)

let fact20Div2' = peval6 fact20Div2Program env0 fenv0 
let Qfact20Div2' = QuotationCompiler.ToFunc (peval6 fact20Div2Program env0 fenv0) 

duration (fun() -> Qfact20Div2' ()) "compiled CPS fact20Div2Program with error handling"// 3628800

