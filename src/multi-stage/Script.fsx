
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
    

// power example

// val power : int -> int code -> int code
// let rec power n x =
//     match n with
//     | 0 -> .<1>. | n -> .<.~x * .~(power (n-1) x)>.

// let power2 = .! .<fun x -> .~(power 2 .<x>.)>.

// val power : int -> Expr<int> -> Expr<int>
let rec power n x = 
    match n with 
    | 0 -> <@ 1 @> | n -> <@ %x * (% power (n - 1) x ) @> 

let power2 = QuotationCompiler.Eval <| lambda (fun x -> power 2 x)
let power2' = QuotationCompiler.Eval <| 
                <@ fun x -> (% lambda (fun x -> power 2 x) ) x @>

power2 10 // 100
power2' 10 // 100