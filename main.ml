open Syntax.Syntax;;
open Kernel.Kernel;;
open Lexer;;
open Lexing;;


let filename = Sys.argv.(1);;


let props =
  let input = open_in filename in
  let filebuf = Lexing.from_channel input in
  (Parser.prog Lexer.read filebuf);;

let s = tptp_to_sequent props;;
let p = find_proof s;;
print_string (format_sequent s);;
