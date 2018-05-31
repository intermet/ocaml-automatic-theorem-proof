open Syntax.Syntax;;
open Kernel.Kernel;;
open Lexer;;
open Lexing;;
open Examples;;


(* Solve fof *)
(* let filename = Sys.argv.(1);;
 * 
 * 
 * let props =
 *   let input = open_in filename in
 *   let filebuf = Lexing.from_channel input in
 *   (Parser.prog Lexer.read filebuf);;
 * 
 * let s = tptp_to_sequent props;;
 * let p = find_proof s;; *)


Random.init 0;;
(* let s = Example.stage1_ex1;;
 * let proof = find_proof s;;
 * print_string (format_proof s proof);; *)


(* Solve all examples *)
List.map (fun s -> find_proof s) (Example.all_ex);;
(* print_string (format_sequent s);; *)

