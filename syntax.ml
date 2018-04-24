module type SYNTAX =
  sig
    type term = 
      | MetaVariable of string * term list
      | Variable of string
      | Constant of string
      | Operator of string * int * term list
                  
    type formula = private 
      | Predicate of string * int * term list
      | And of formula * formula
      | True
      | Or of formula * formula
      | False
      | Implies of formula * formula
      | Forall of term * formula
      | Exists of term * formula

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
    val forall : term -> formula -> formula
    val exists : term -> formula -> formula

    val meta_replace : formula -> formula
    val const_replace : formula -> formula * term 
    val add_cst_fc_f : term -> formula -> formula

      
  end

  
module Syntax : SYNTAX = struct
  type term = 
    | MetaVariable of string * term list
    | Variable of string
    | Constant of string
    | Operator of string * int * term list
                
  type formula = 
    | Predicate of string * int * term list
    | And of formula * formula
    | True
    | Or of formula * formula
    | False
    | Implies of formula * formula
    | Forall of term * formula
    | Exists of term * formula
              
  exception SyntaxError;;
  
  let metavariable name forb = MetaVariable(name, forb);;
  
  let variable name = Variable(name);;

  let constant name = Constant(name);;
          
  let operator name argc terms = (assert (argc >= 0 && List.length terms = argc)); Operator (name, argc, terms)

  let predicate name argc terms = (assert (argc >= 0 && List.length terms = argc)); Predicate (name, argc, terms)

  let _and formula1 formula2 = And(formula1, formula2)

  let _true = True

  let _or formula1 formula2 = Or(formula1, formula2)

  let _false =  False

  let implies formula1 formula2 = Implies(formula1,formula2)

  let forall term formula1 = match term with
    | Variable(_) -> Forall (term, formula1)
    | _ -> raise SyntaxError;;
                              
  let exists term formula1 = match term with
    | Variable(_) -> Exists(term, formula1)
    | _ -> raise SyntaxError;;

  let rec map f l = match l with
    | [] -> []
    | x::q -> (f x)::(map f q);;

  
  let meta_replace f =
    let rec aux form var metavar = match form with
      | True | False -> form
      | Predicate(name, n, terms) -> Predicate(name, n, map (fun t -> if t = var then metavar else t) terms)
      | And(f1, f2) -> And(aux f1 var metavar, aux f2 var metavar)
      | Or(f1, f2) -> Or(aux f1 var metavar, aux f2 var metavar)
      | Implies(f1, f2) -> Implies(aux f1 var metavar, aux f2 var metavar)
      | Forall(v, f1) -> Forall(v, aux f1 var metavar)
      | Exists(v, f1) -> Exists(v, aux f1 var metavar)
    in match f with
       | Forall(Variable(x), form) -> aux form (Variable(x)) (MetaVariable("\\_" ^ (String.uppercase_ascii x), []))
       | Exists(Variable(x), form) -> aux form (Variable(x)) (MetaVariable("\\_" ^ (String.uppercase_ascii x), []))
       | _ -> raise SyntaxError;;

  
  let add_cst_fc_t cst t = match t with
    | MetaVariable(x, fc) -> MetaVariable(x, cst::fc)
    | _ -> t;;

  let rec add_cst_fc_f cst form = match form with
    | True | False -> form
    | Predicate(name, n , terms) -> Predicate(name, n, map (add_cst_fc_t cst) terms)
    | And(f1, f2) -> And(add_cst_fc_f cst f1, add_cst_fc_f cst f2)
    | Or(f1, f2) -> Or(add_cst_fc_f cst f1, add_cst_fc_f cst f2)  
    | Implies(f1, f2) -> Implies(add_cst_fc_f cst f1, add_cst_fc_f cst f2)
    | Forall(v, f1) -> Forall(v, add_cst_fc_f cst f1)
    | Exists(v, f1) -> Exists(v, add_cst_fc_f cst f1);;
  
  let const_replace f =
    let rec aux form var cst = match form with
      | True | False -> form
      | Predicate(name, n ,terms) -> Predicate(name, n ,map (fun t -> if t = var then cst else t) terms)
      | And(f1, f2) -> And(aux f1 var cst, aux f2 var cst)
      | Or(f1, f2) -> Or(aux f1 var cst, aux f2 var cst)
      | Implies(f1, f2) -> Implies(aux f1 var cst, aux f2 var cst)
      | Forall(v, f1) -> Forall(v, aux f1 var cst)
      | Exists(v, f1) -> Exists(v, aux f1 var cst)
    in match f with
       | Forall(Variable(x), form) -> let c = Constant("\\_" ^ x) in
                                      let ff = aux form (Variable(x)) c in add_cst_fc_f c ff, c
       | Exists(Variable(x), form) -> let c = Constant("\\_" ^ x) in
                                      let ff = aux form (Variable(x)) c in add_cst_fc_f c ff, c
       | _ -> raise SyntaxError;;

end
                           

                           
