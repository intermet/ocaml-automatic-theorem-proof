{
   open Lexing
   open Parser

    let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
	{ pos with pos_bol = lexbuf.lex_curr_pos;
		pos_lnum = pos.pos_lnum + 1
	}
}

let white = [' ' '\t']+
let new_line = '\r' | '\n' | "\r\n" 
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read = parse
     | "%" {comment lexbuf}
     | white {read lexbuf}
     | new_line {next_line lexbuf; read lexbuf}
     | "fof" {FOF}
     | "(" {LPAR}
     | ")" {RPAR}
     | "axiom" {AXIOM}
     | "hypothesis" {HYP}
     | "conjecture" {CONJ}
     | "!" {FORALL}
     | "?" {EXISTS}
     | "[" {LBRAK}
     | "]" {RBRAK}
     | ":" {COLON}
     | "=>" {IMPLIES}
     | "<=>" {EQUIV}
     | "&" {AND}
     | "=" {EQUAL}
     | "," {COMMA}
     | "." {DOT}
     | id {STRING (Lexing.lexeme lexbuf)} 
     | eof {EOF}
and comment = parse
     | new_line {read lexbuf}
     | _ {comment lexbuf}