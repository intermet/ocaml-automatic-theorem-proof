module type SYNTAX =
  sig
    type term = 
      | MetaVariable of string * term list
      | Variable of string
      | Constant of string
      | Operator of string * term list
                  
    type formula = private 
      | Predicate of string * term list
      | And of formula * formula
      | True
      | Or of formula * formula
      | False
      | Implies of formula * formula
      | Forall of string * formula
      | Exists of string * formula

    exception SyntaxError
                
    val variable : string -> term
    val metavariable : string -> term list ->term
    val constant : string -> term
    val operator : string -> int -> term list -> term

    val predicate : string -> int -> term list -> formula
    val _and : formula -> formula -> formula
    val _true : formula
    val _or : formula -> formula -> formula
    val _false : formula
    val implies : formula -> formula -> formula
    val forall : string -> formula -> formula
    val exists : string -> formula -> formula

    val meta_replace : formula -> formula
    val const_replace : formula -> formula * term 
    val add_cst_fc_f : term -> formula -> formula
    val replace_cst_var : formula -> formula

    val concatenate : string list -> string
    val format_term : term -> string
    val format_formula : formula -> string
  end

  
module Syntax : SYNTAX = struct
  type term = 
    | MetaVariable of string * term list
    | Variable of string
    | Constant of string
    | Operator of string * term list
                
  type formula = 
    | Predicate of string * term list
    | And of formula * formula
    | True
    | Or of formula * formula
    | False
    | Implies of formula * formula
    | Forall of string * formula
    | Exists of string * formula
              
  exception SyntaxError;;
  
  let metavariable name forb = MetaVariable(name, forb);;
  
  let variable name = Variable(name);;

  let constant name = Constant(name);;
          
  let operator name argc terms = (assert (argc >= 0 && List.length terms = argc)); Operator (name, terms)

  let predicate name argc terms = (assert (argc >= 0 && List.length terms = argc)); Predicate (name, terms)

  let _and formula1 formula2 = And(formula1, formula2)

  let _true = True

  let _or formula1 formula2 = Or(formula1, formula2)

  let _false =  False

  let implies formula1 formula2 = Implies(formula1,formula2)

  let forall x f = Forall(x, f);;
                              
  let exists x f = Exists(x, f);;

  let rec map f l = match l with
    | [] -> []
    | x::q -> (f x)::(map f q);;

  
  let meta_replace f =
    let rec aux form var metavar = match form with
      | True | False -> form
      | Predicate(name, terms) -> Predicate(name, map (fun t -> if t = var then metavar else t) terms)
      | And(f1, f2) -> And(aux f1 var metavar, aux f2 var metavar)
      | Or(f1, f2) -> Or(aux f1 var metavar, aux f2 var metavar)
      | Implies(f1, f2) -> Implies(aux f1 var metavar, aux f2 var metavar)
      | Forall(v, f1) -> Forall(v, aux f1 var metavar)
      | Exists(v, f1) -> Exists(v, aux f1 var metavar)
    in match f with
       | Forall(x, form) -> aux form (Variable(x)) (MetaVariable("\\_" ^ (String.uppercase_ascii x), []))
       | Exists(x, form) -> aux form (Variable(x)) (MetaVariable("\\_" ^ (String.uppercase_ascii x), []))
       | _ -> raise SyntaxError;;

  
  let add_cst_fc_t cst t = match t with
    | MetaVariable(x, fc) -> MetaVariable(x, cst::fc)
    | _ -> t;;

  let rec add_cst_fc_f cst form = match form with
    | True | False -> form
    | Predicate(name, terms) -> Predicate(name, map (add_cst_fc_t cst) terms)
    | And(f1, f2) -> And(add_cst_fc_f cst f1, add_cst_fc_f cst f2)
    | Or(f1, f2) -> Or(add_cst_fc_f cst f1, add_cst_fc_f cst f2)  
    | Implies(f1, f2) -> Implies(add_cst_fc_f cst f1, add_cst_fc_f cst f2)
    | Forall(v, f1) -> Forall(v, add_cst_fc_f cst f1)
    | Exists(v, f1) -> Exists(v, add_cst_fc_f cst f1);;
  
  let const_replace f =
    let rec aux form var cst = match form with
      | True | False -> form
      | Predicate(name, terms) -> Predicate(name, map (fun t -> if t = var then cst else t) terms)
      | And(f1, f2) -> And(aux f1 var cst, aux f2 var cst)
      | Or(f1, f2) -> Or(aux f1 var cst, aux f2 var cst)
      | Implies(f1, f2) -> Implies(aux f1 var cst, aux f2 var cst)
      | Forall(v, f1) -> Forall(v, aux f1 var cst)
      | Exists(v, f1) -> Exists(v, aux f1 var cst)
    in match f with
       | Forall(x, form) -> let c = Constant("\\_" ^ x) in
                                      let ff = aux form (Variable(x)) c in add_cst_fc_f c ff, c
       | Exists(x, form) -> let c = Constant("\\_" ^ x) in
                                      let ff = aux form (Variable(x)) c in add_cst_fc_f c ff, c
       | _ -> raise SyntaxError;;

  let rec replace_cst_var f =
    let rec aux1 t c = match t with
      | Constant(name) when List.mem name c -> Variable(name)
      | Operator(name, terms) -> Operator(name, List.map (fun x-> aux1 x c) terms)
      | _ -> t
    in
    let rec aux2 f c = match f with
      | Predicate(name, terms) -> Predicate(name, List.map (fun x-> aux1 x c) terms)
      | And(f1, f2) -> And(aux2 f1 c, aux2 f2 c)
      | True | False -> f
      | Or(f1, f2) -> Or(aux2 f1 c, aux2 f2 c)
      | Implies(f1, f2) -> Implies(aux2 f1 c, aux2 f2 c)
      | Forall(x, f1) -> Forall(x, aux2 f1 (x::c))
      | Exists(x, f1) -> Exists(x, aux2 f1 (x::c))
    in aux2 f [];;

  
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

end
                           

                           
