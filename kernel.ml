open Syntax.Syntax;;
open Mgu.Mgu;;
open Tptp;;
 
module FormulaSet =
  Set.Make(
      struct
        let compare = Pervasives.compare
        type t = formula
      end
    )

module type KERNEL =
  sig
    type sequent =
      | Invalid
      | Done
      | NonSelected of FormulaSet.t * FormulaSet.t
      | SelectedL of FormulaSet.t * FormulaSet.t * formula
      | SelectedR of FormulaSet.t * FormulaSet.t * formula

    type proof =
      | None
      | SelL of formula * proof
      | SelR of formula * proof 
      | IniL
      | IniR
      | ImpL of proof * proof
      | ImpR of proof
      | AndL of proof
      | AndR of proof * proof
      | TrueL of proof
      | TrueR
      | OrL of proof * proof
      | OrR of proof
      | FalseL
      | FalseR of proof
      | ForallL of proof
      | ForallR of proof
      | ExistsL of proof
      | ExistsR of proof

    val empty : FormulaSet.t
    val singleton : formula -> FormulaSet.t
    val add : formula -> FormulaSet.t -> FormulaSet.t

    val selL : sequent  -> formula -> sequent 
    val selR : sequent  -> formula -> sequent 

    val iniL : sequent -> sequent 
    val iniR : sequent -> sequent 

    val impL : sequent -> sequent * sequent
    val impR : sequent -> sequent

    val andL : sequent -> sequent
    val andR : sequent -> sequent * sequent

    val trueL : sequent -> sequent
    val trueR : sequent -> sequent

    val orL : sequent -> sequent * sequent
    val orR : sequent -> sequent

    val falseL : sequent -> sequent
    val falseR : sequent -> sequent

    val forallL : sequent -> sequent
    val forallR : sequent -> sequent

    val existsL : sequent -> sequent
    val existsR : sequent -> sequent

    val search : sequent -> int -> bool * proof

    val format_term : term -> string
    val format_formula : formula -> string 
    val format_sequent : sequent -> string
    val format_proof : sequent -> proof -> string 
    val format_tex : sequent -> proof -> string

    val find_proof : sequent -> proof

    val tptp_to_sequent : prop list -> sequent
      
       
  end


module Kernel : KERNEL = struct
  type sequent =
    | Invalid
    | Done
    | NonSelected of FormulaSet.t * FormulaSet.t
    | SelectedL of FormulaSet.t * FormulaSet.t * formula
    | SelectedR of FormulaSet.t * FormulaSet.t * formula;;
                 
  type proof =
    | None
    | SelL of formula * proof
    | SelR of formula * proof 
    | IniL
    | IniR
    | ImpL of proof * proof
    | ImpR of proof
    | AndL of proof
    | AndR of proof * proof
    | TrueL of proof
    | TrueR
    | OrL of proof * proof
    | OrR of proof
    | FalseL
    | FalseR of proof
    | ForallL of proof
    | ForallR of proof
    | ExistsL of proof
    | ExistsR of proof;;



  exception Error;;
  
  let add = FormulaSet.add;;
  let mem = FormulaSet.mem;;
  let remove = FormulaSet.remove;;
  let find_first = FormulaSet.find_first;;
  let elements = FormulaSet.elements;;
  let empty = FormulaSet.empty;;
  let singleton  = FormulaSet.singleton;;

  let rec any f l = match l with
    | [] -> false
    | x::q -> (f x) || (any f q);;

  let principal seq = match seq with
    | SelectedL(_, _, p) -> p
    | SelectedR(_, _, p) -> p
    | _ -> raise Error;;
                   
  let selL seq formula = match seq with
    | NonSelected(left, right) when mem formula left -> SelectedL(left, right, formula)
    | _ -> Invalid;;
  
  let selR seq formula = match seq with
    | NonSelected(left, right) when mem formula right -> SelectedR(left, right, formula)
    | _ -> Invalid;;

  let iniL seq = match seq with
    | SelectedL(left, right, f) -> if any (unifiable  f) (elements right) then Done else Invalid
    | _ -> Invalid;;
  
  let iniR seq = match seq with
    | SelectedR(left, right, f) -> if mem f left then Done else Invalid 
    | _ -> Invalid;;
  
  let impL seq = match seq  with
    | SelectedL(left, right, Implies(c, a)) -> NonSelected(left, add c right),
                                              NonSelected(add a left, right)
    | _ -> Invalid, Invalid;;

  let impR seq = match seq with
    | SelectedR(left, right, Implies(a, Implies(b, c))) -> SelectedR(add a left, remove (implies a (implies b c)) right, implies b c)
    | SelectedR(left, right, Implies(a, c)) -> NonSelected(add a left, remove (implies a c) (add c right))
    | _ -> Invalid;;

  let andL seq = match seq with
    | SelectedL(left, right, And(a, b)) -> NonSelected(remove (_and a b) (add a (add b left)), right)
    | _ -> Invalid;;

  let andR seq = match seq with
    | SelectedR(left, right, And(c, d)) -> NonSelected(left, remove (_and c d) (add c right)),
                                          NonSelected(left, remove (_and c d) (add d right))
    | _ -> Invalid, Invalid;;

  let trueL seq = match seq with
    | SelectedL(left, right, True) -> NonSelected(left, right)
    | _ -> Invalid;;

  let trueR seq = match seq with
    | SelectedR(_, _, True) -> Done
    | _ -> Invalid;;

  let orL seq = match seq with
    | SelectedL(left, right, Or(a, b)) -> NonSelected(remove (_or a b) (add a left), right), NonSelected(remove (_or a b) (add b left), right)
    | _ -> Invalid, Invalid;;

  let orR seq = match seq with
    | SelectedR(left, right, Or(c, d)) -> NonSelected(left, remove (_or c d) (add c (add d right)))
    | _ -> Invalid;;

  let falseL seq = match seq with
    | SelectedL(_, _, False) -> Done 
    | _ -> Invalid;;

  let falseR seq = match seq with
    | SelectedR(left, right, False) -> NonSelected(left, right)
    | _ -> Invalid;;


  let forallL seq = match seq with
    | SelectedL(left, right, Forall(x, form)) -> let p = principal seq in
                                                 let s = add (meta_replace p) left in
                                                 NonSelected(s, right) 
    | _ -> Invalid;;

  let forallR seq = match seq with
    | SelectedR(left, right, Forall(x, form)) -> let p = principal seq in
                                                 let f, c = const_replace p in
                                                 let s = add (add_cst_fc_f c f) right in
                                                 let newright = FormulaSet.map (add_cst_fc_f c) s in
                                                 let newleft = FormulaSet.map (add_cst_fc_f c) left in
                                                 NonSelected(newleft, newright) 
    | _ -> Invalid;;


  let existsL seq = match seq with
    | SelectedL(left, right, Exists(x, form)) -> let p = principal seq in
                                                 let f, c = const_replace p in
                                                 let s = add (add_cst_fc_f c f) left in
                                                 let newleft = FormulaSet.map (add_cst_fc_f c) s in
                                                 let newright = FormulaSet.map (add_cst_fc_f c) right in
                                                 NonSelected(newleft, newright) 
    | _ -> Invalid;;

  let existsR seq = match seq with
    | SelectedR(left, right, Exists(x, form)) -> let p = principal seq in
                                                 let s = add (meta_replace p) right in
                                                 NonSelected(left, s)
    | _ -> Invalid;;
  
  let rec any f l = match l with
    | [] -> false
    | x::q -> (f x) || (any f q);;
  
  let rec map f l = match l with
    | [] -> []
    | x::q -> f(x)::(map f q);;

  let rec select f sequent =
    let rec auxL l = match l with
      | [] -> false, None
      | x::q -> let b, p = f(selL sequent x) in if b then b, SelL(x, p) else auxL q
    in
    let rec auxR l = match l with
      | [] -> false, None
      | x::q -> let b, p = f(selR sequent x) in if b then b, SelR(x, p) else auxR q
    in match sequent with
       | NonSelected(left, right) -> let b, p = auxL (elements left) in if b then b,p else auxR (elements right)
       | _ -> false, None;;


  let random_pick l =
    let n = List.length l in
    let i = Random.int n in
    let rec aux l i acc = if i == 0 then (List.hd l, acc @ (List.tl l))
                          else aux (List.tl l) (i-1) ((List.hd l)::acc)
    in
    aux l i [];;

  
  let rec random_select f seq =
    let rec aux left right = match left, right with
      | [], [] -> false, None
      | [], _ -> let x, r = random_pick right in let b, p = f(selR seq x) in
                                              if b then b, SelR(x, p)
                                              else aux left r

      | _, [] -> let x, l = random_pick left in let b, p = f(selL seq x) in
                                              if b then b, SelL(x, p)
                                              else aux l right
      | _, _ -> if Random.bool() then
                  begin
                    let x, r = random_pick right in let b, p = f(selR seq x) in
                                                    if b then b, SelR(x, p)
                                                    else aux left r
                  end
                else
                  begin
                    let x, l = random_pick left in let b, p = f(selL seq x) in
                                                   if b then b, SelL(x, p)
                                                   else aux l right
                  end
    in match seq with
       | NonSelected(left, right) -> aux (elements left) (elements right)
       | _ -> false, None
                
  
  let rec search sequent bound = match sequent, bound with
      | _, _ when bound < 0 -> false, None
      | Invalid, _ -> false, None
      | Done, _ -> true, None
      | NonSelected(_, _), _ -> random_select (fun x -> search x (bound - 1)) sequent 
      | SelectedL(_, _, Predicate(_)), _ -> let b, p = search (iniL sequent) (bound - 1) in
                                            b, IniL
      | SelectedR(_, _, Predicate(_)), _ -> let b, p = search (iniR sequent) (bound - 1) in
                                            b, IniR
      | SelectedL(_, _, Implies(_)), _ -> let s1, s2 = impL sequent in
                                          let b1, p1 = search s1 (bound - 1) and b2, p2 = search s2 (bound - 1) in
                                          if (b1 && b2) then true, ImpL(p1, p2) else false, None
      | SelectedR(_, _, Implies(_)), _ -> let b, p = search (impR sequent) (bound - 1) in
                                          if b then b, ImpR p else false, None
      | SelectedL(_, _, And(_)), _ -> let b, p = search (andL sequent) (bound - 1) in
                                      if b then b, AndL p else false, None
      | SelectedR(_, _, And(_)), _ -> let s1, s2 = andR sequent in
                                      let b1, p1 = search s1 (bound - 1) and b2, p2 = search s2 (bound - 1) in
                                      if (b1 && b2) then true, AndR(p1, p2) else false, None
      | SelectedL(_, _, True), _ -> let b, p = search (trueL sequent) (bound - 1) in
                                    if b then b, TrueL p else false, None
      | SelectedR(_, _, True), _ -> let b, p = search (trueR sequent) (bound - 1) in
                                    if b then b, TrueR else false, None
      | SelectedL(_, _, Or(_)), _ -> let s1, s2 = orL sequent in
                                     let b1, p1 = search s1 (bound - 1) and b2, p2 = search s2 (bound - 1) in
                                     if b1 && b2 then b1 && b2, OrL(p1, p2) else false, None
      | SelectedR(_, _, Or(_)), _ -> let b, p = search (orR sequent) (bound - 1) in
                                     if b then b, OrR(p) else false, None
      | SelectedL(_, _, False), _ -> let b, p = search (falseL sequent) (bound - 1) in
                                     if b then b, FalseL else false, None
      | SelectedR(_, _, False), _ -> let b, p = search(falseR sequent) (bound - 1) in
                                     if b then b, FalseR(p) else false, None
      | SelectedL(_, _, Forall(_)), _ -> let b, p = search (forallL sequent) (bound - 1) in
                                         if b then b, ForallL(p) else false, None
      | SelectedR(_, _, Forall(_)), _ -> let b, p = search (forallR sequent) (bound - 1) in
                                         if b then b, ForallR(p) else false, None
      | SelectedL(_, _, Exists(_)), _ -> let b, p = search (existsL sequent) (bound - 1) in
                                         if b then b, ExistsL(p) else false, None
      | SelectedR(_, _, Exists(_)), _ -> let b, p = search (existsR sequent) (bound - 1) in
                                         if b then b, ExistsR(p) else false, None;;
  
  let rec concatenate list_str = match list_str with
    | [] -> ""
    | t::[] -> t
    | t::q -> t ^ "," ^ concatenate q;;

  let rec format_term term = match term with
    | MetaVariable(name, fc) -> name ^ "(" ^ concatenate (map format_term fc) ^ ")"
    | Variable(name) -> name
    | Constant(name) -> name
    | Operator(name, terms) -> name ^ "(" ^ concatenate (map format_term terms)  ^ ")" ;;

  let rec format_formula formula = match formula with
    | Predicate(name, terms) when terms = [] -> name
    | Predicate(name, terms) -> name ^ "(" ^ concatenate (map format_term terms) ^ ")"
    | And(f1, f2)  ->  format_formula f1 ^ "\\land " ^ format_formula f2
    | True -> "\\top "
    | Or(f1, f2) -> format_formula f1 ^ "\\lor " ^ format_formula f2
    | False -> "\\bot "
    | Implies(f1, f2) -> "(" ^ format_formula f1 ^ "\\Rightarrow " ^ format_formula f2 ^ ")"
    | Forall(name, f1) -> "\\forall " ^ name ^ "." ^ format_formula f1
    | Exists(name, f1) -> "\\exists " ^ name ^ "." ^ format_formula f1;;

  let rec format_formulas formulas =
    let formulas = elements formulas in
    concatenate (map format_formula formulas);;

  let rec format_sequent sequent = match sequent with
    | NonSelected(left, right) -> (format_formulas left) ^ "\\vdash "
                                  ^ (format_formulas right) 
    | SelectedL(left, right, principal) -> (format_formulas left) ^ ",[" ^ format_formula principal ^ "]"
                                           ^ "\\vdash "
                                           ^ (format_formulas right)
    | SelectedR(left, right, principal) -> (format_formulas left)
                                           ^ "\\vdash "
                                           ^ "[" ^ format_formula principal ^ "],"
                                           ^ (format_formulas right)
    | Done -> "DONE"
    | Invalid -> "ERROR_INVALID";;

  let rec format_proof seq proof = match proof with
    | SelL(principal, p) -> "\\prftree[r]{left-sel}\n{" ^ (format_proof (selL seq principal) p) ^ "}"
                         ^ "\n{" ^ (format_sequent seq) ^ "}"
    | SelR(principal, p) -> "\\prftree[r]{right-sel}\n{" ^ (format_proof (selR seq principal) p) ^ "}"
                         ^ "\n{" ^ (format_sequent seq) ^ "}"
    | IniL -> "\\prftree[r]{iniL}{}\n{" ^ (format_sequent seq) ^ "}"
    | IniR -> "\\prftree[r]{iniR}{}\n{" ^ (format_sequent seq) ^ "}"
    | ImpL(p1, p2) -> let s1, s2 = impL seq in
                           "\\prftree[r]{$\\Rightarrow L$}\n{\\prfassumption\n{"^ (format_proof s1 p1) ^ "}\n{"
                           ^ (format_proof s2 p2) ^ "}}\n{"
                           ^ (format_sequent seq) ^ "}" 
    | ImpR(p) -> "\\prftree[r]{$\\Rightarrow R$}\n{" ^ (format_proof (impR seq) p)  ^  "}"
                      ^ "\n{" ^ (format_sequent seq) ^ "}"
    | AndL(p) -> "\\prftree[r]{$\\land L$}\n{" ^ (format_proof (andL seq) p) ^ "}"
                    ^ "\n{" ^ (format_sequent seq) ^ "}"
    | AndR(p1, p2) -> let s1, s2 = andR seq in
                           "\\prftree[r]{$\\land R$}\n{\\prfassumption\n{" ^ (format_proof s1 p1) ^ "}\n{"
                           ^ (format_proof s2 p2) ^ "}}"
                           ^ "\n{" ^ (format_sequent seq) ^ "}"
    | TrueL(p) -> "\\prftree[r]{$\\top L$}\n{" ^ (format_proof (trueL seq) p) ^ "}"
                       ^ "\n{" ^ (format_sequent seq) ^ "}"
    | TrueR-> "\\prftree[r]{$\\top R$}{}\n{" ^ (format_sequent seq) ^ "}" 
    | OrL(p1, p2)  -> let s1, s2 = orL seq in
                           "\\prftree[r]{\\lor L}\n{\\prfassumption\n{" ^ (format_proof s1 p1) ^ "}\n{"
                           ^ (format_proof s2 p2) ^ "}}"
                           ^ "\n{" ^ (format_sequent seq) ^ "}"
    | OrR(p) -> "\\prftree[r]{$\\lor R$}\n{" ^ (format_proof (orR seq) p) ^ "}"
                     ^ "\n{" ^ (format_sequent seq) ^ "}"
    | FalseL-> "\\prftree[r]{$\\bot L$}{}\n{" ^ (format_sequent seq) ^ "}"
    | FalseR(p) -> "\\prftree[r]{$\\bot R$}\n{" ^ (format_proof (falseR seq) p) ^ "}"
                      ^ "\n{" ^ (format_sequent seq) ^ "}"
    | ForallL(p) -> "\\prftree[r]{$\\forall L$}\n{" ^ (format_proof (forallL seq) p) ^ "}"
                    ^ "\n{" ^ (format_sequent seq) ^ "}"
    | ForallR(p) -> "\\prftree[r]{$\\forall R$}\n{" ^ (format_proof (forallR seq) p) ^ "}"
                    ^ "\n{" ^ (format_sequent seq) ^ "}"
    | ExistsL(p) -> "\\prftree[r]{$\\exists L$}\n{" ^ (format_proof (existsL seq) p) ^ "}"
                    ^ "\n{" ^ (format_sequent seq) ^ "}"
    | ExistsR(p) -> "\\prftree[r]{$\\exists R$}\n{" ^ (format_proof (existsR seq) p) ^ "}"
                    ^ "\n{" ^ (format_sequent seq) ^ "}"
    | _ -> "ERROR"                  

  let format_tex seq proof =
    let s = format_proof seq proof in
    "\\documentclass[13pt]{article}\n\\usepackage{prftree}\n\\usepackage[a1paper, margin=0in]{geometry}\n\\usepackage{lscape}\n\\begin{document}\n\\begin{landscape}\n\\begin{displaymath}"^s^"\n\\end{displaymath}\n\\end{landscape}\n\\end{document}";;

  let find_proof seq =
    let rec aux bound = 
      let b, proof = search seq bound in
      if b then begin print_string "proved \n"; proof end else aux (2 + bound)
    in aux 1;;


  let tptp_to_sequent props =
    let rec aux p acc = match p, acc with
      | [], NonSelected(left, right) -> NonSelected(FormulaSet.map replace_cst_var left,
                                                    FormulaSet.map replace_cst_var right)
      | Axiom(f)::q, NonSelected(left, right) -> aux q (NonSelected(add f left, right))
      | Hyp(f)::q, NonSelected(left, right) -> aux q (NonSelected(add f left, right))
      | Conj(f)::q, NonSelected(left, right) -> aux q (NonSelected(left, add f right))
      | _ -> raise Error
    in aux props (NonSelected(empty, empty));;
                                               
         
end
