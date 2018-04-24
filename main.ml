open Kernel.Kernel;;
open Syntax.Syntax;;
open Mgu.Mgu;;

let x = variable "x";;
let y = variable "y";;
let px = predicate "p" 1 (x::[]);;
let py = predicate "p" 1 (y::[]);;
let fy = forall y py;;
let f = implies px fy;;
let thm = exists x f;;
let seq = NonSelected(empty, singleton thm);;

print_string (format_proof seq (find_proof seq));;
(*
let x = variable "x";;
let p =predicate "p" 1 (x::[]);;
let f = implies p _false;;        
let ff = implies f _false;;
let fff = forall x ff;;
let g = forall x p;;
let gg = implies g _false;;
let ggg = implies gg _false;;
let h = implies fff ggg;;
let seq = NonSelected(empty, singleton h);;
print_string (format_proof seq (find_proof seq));;
 *)
(*let x = variable "x";;
let y = constant "y";;
let p = predicate "p" 2 (x::y::[]);;
let f = forall (variable "x") p;; 
let g = remplace f x (constant "z");;
print_string (format_formula f);;
 *)

