open Syntax.Syntax;;

type prop =
  | Axiom of formula
  | Conj of formula
  | Hyp of formula;;  



let rec parse_forall v f = match v with
  | [] -> f
  | Constant(x)::q -> parse_forall q (forall x f)
  | _ -> raise SyntaxError;;

let rec parse_exists v f = match v with
  | [] -> f
  | Constant(x)::q -> parse_exists q (exists x f)
  | _ -> raise SyntaxError;;
