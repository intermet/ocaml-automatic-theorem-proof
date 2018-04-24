open Syntax.Syntax;;

module type MGU =
  sig
    type disagrement =
      | NonUnifiable
      | NoDisagrement
      | Dis of term * term

    val unifiable : formula -> formula -> bool
  end


module Mgu : MGU = struct

  type disagrement =
    | NonUnifiable
    | NoDisagrement
    | Dis of term * term

  let rec mem l x = match l with
    | [] -> false
    | y::q -> (x=y) || (mem q x);;
           
  let rec any f l = match l with
    | [] -> false
    | t::q -> (f t) || (any f q);;

  let rec map f l = match l with
    | [] -> []
    | t::q -> (f t)::(map f q);;

  let rec occurs f1 f2 = match f2 with
    | _ when f1 = f2 -> true
    | Constant(_) -> false
    | MetaVariable(_) -> false
    | Variable(_) -> false
    | Operator(_, _, terms) -> any (occurs f1) terms;; 
           
  let rec find_disagrement f1 f2 = match f1, f2 with
    | Constant(n1), Constant(n2) when n1 = n2 -> NoDisagrement
    | Constant(_), Constant(_) -> NonUnifiable
    | Operator(name1, n1, _), Operator(name2, n2, _) when not (name1 = name2) -> NonUnifiable
    | Operator(_, _, []), Operator(_, _, []) -> NoDisagrement
    | Operator(name1, n1, t1::q1), Operator(name2, n2, t2::q2) -> let d = find_disagrement t1 t2 
                                                                  in
                                                                  let op1 = operator name1 (n1-1) q1
                                                                  and op2 = operator name2 (n2-1) q2 in
                                                                  if d = NoDisagrement
                                                                  then
                                                                    find_disagrement op1 op2 
                                                                  else
                                                                    d
                                                                    
    | MetaVariable(n1, _), MetaVariable(n2, _) when n1 = n2 -> NoDisagrement 
    | MetaVariable(_), MetaVariable(_) -> Dis(f1, f2)
    | Constant(_), MetaVariable(_, fc) -> if mem fc f1 then NonUnifiable else Dis(f1, f2)
    | MetaVariable(_, fc), Constant(_) -> if mem fc f2 then NonUnifiable else Dis(f2, f1)
    | Operator(_), MetaVariable(_) when not (occurs f2 f1) -> Dis(f1, f2)
    | MetaVariable(_), Operator(_) when not (occurs f1 f2) -> Dis(f2, f1)
    | _, _ -> NonUnifiable;;

  (* dis = Dis(term, MetaVariable) *)
  let rec substitute dis f = match dis, f with
    | Dis(t1, mv), MetaVariable(_) when f = mv -> t1
    | Dis(t1, mv), Operator(name, n, terms) -> operator name n (map (substitute dis) terms)
    | _, _ -> f;;

  let rec _unifiable f1 f2 = match find_disagrement f1 f2  with
    | NonUnifiable -> false
    | NoDisagrement -> true
    | Dis(t1, t2) -> _unifiable (substitute (Dis(t1, t2)) f1) (substitute (Dis(t1, t2)) f2);;

  let unifiable f1 f2 = match f1, f2 with
    | Predicate(name1, n1, terms1), Predicate(name2, n2, terms2)
         when (name1 = name2) && (n1 = n2) -> let op1 = operator "_p" n1 terms1
                                                and op2 = operator "_p" n1 terms2
                                              in _unifiable op1 op2
    | _ -> false;;
      

end
(*
let x = metavariable "X";;
let y = metavariable "Y";;
let a = constant "a";;
let b = constant  "b";;
let plus1 = operator "plus"  2 (x::y::[]);;
let plus2 = operator "plus"  2 (a::b::[]);;
let p = predicate "p" 1 (plus1::[]);;
let pp = predicate "pp" 1 (plus2::[]);;
                    
let b = Mgu.unifiable p pp;;
if b then print_string "ok" else print_string "not ok";;
 *)
