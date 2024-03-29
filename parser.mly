%{
    open Syntax.Syntax
    open Tptp
%}
%token <string> STRING
%token FOF
%token LPAR RPAR
%token AXIOM
%token HYP
%token CONJ
%token FORALL
%token EXISTS
%token LBRAK RBRAK
%token COLON
%token IMPLIES
%token EQUIV
%token AND
%token EQUAL
%token COMMA
%token DOT
%token EOF


%start <Tptp.prop list> prog
%%

prog:
  | EOF {[]}
  | p = prog2 DOT q = prog {p::q} 

prog2:
  | FOF LPAR name = STRING COMMA AXIOM COMMA f = form RPAR {Axiom(f)}
  | FOF LPAR name = STRING COMMA HYP COMMA f = form RPAR {Hyp(f)}
  | FOF LPAR name = STRING COMMA CONJ COMMA f = form RPAR {Conj(f)}

form:
  | LPAR f = form RPAR {f}
  | f1 = form AND f2 = form {_and f1 f2}
  | f1 = form IMPLIES f2 = form {implies f1 f2}
  | f1 = form EQUIV f2 = form {_and (implies f1 f2) (implies f2 f1)}
  | FORALL LBRAK v = terms RBRAK COLON f = form { parse_forall v f }
  | EXISTS LBRAK v = terms RBRAK COLON f = form { parse_exists v f }
  | p1 = term EQUAL p2 = term {predicate "=" 2 (p1::p2::[])}
  | name = STRING LPAR t = terms RPAR {predicate name  (List.length t) t}
  | f = STRING {predicate f 0 []}

term:
  | c = STRING {constant c}
  | v = STRING LPAR c = terms RPAR {operator v (List.length c) c} 

terms:
  | c = separated_list(COMMA, term) {c}
