open Syntax.Syntax;;
open Kernel.Kernel;;
(* open Lexer;;
 * open Lexing;; *)


let filename = Sys.argv.(1);;


let props =
  let input = open_in filename in
  let filebuf = Lexing.from_channel input in
  (Parser.prog Lexer.read filebuf);;

let s = tptp_to_sequent props;;
let p = find_proof s;;

(* print_string (format_sequent s);; *)

(* Random.init 0;;
 * let x = variable "x";;
 * let y = variable "y";;
 * 
 * let p1 = predicate "p" 1 (x::[]);;
 * let p2 = predicate "p" 1 (x::[]);;
 * 
 * let s = NonSelected(singleton p1, singleton p2);;
 * let proof = find_proof s;;
 * print_string (format_proof s proof);; *)

