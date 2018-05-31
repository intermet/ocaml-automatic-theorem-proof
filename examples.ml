open Syntax.Syntax;;
open Kernel.Kernel;;

module Example = struct
  let stage1_ex1 =
    let p = predicate "p" 0 ([]) in
    NonSelected(empty, singleton (implies _false p));;
  
  let stage1_ex2 =
    let p = predicate "p" 0 ([]) in
    NonSelected(empty, singleton (_or p (implies p _true)));;

  let stage1_ex3 =
    let p = predicate "p" 0 ([]) in
    let q = predicate "q" 0 ([]) in
    NonSelected(empty, singleton (implies (implies (implies p q) (p)) (p)));;

  let stage1_ex4 =
    let p = predicate "p" 0 ([]) in
    NonSelected(empty, singleton (implies (implies (implies p _false) _false) p));;

  let stage1_ex5 =
    let p = predicate "p" 0 ([]) in
    let q = predicate "q" 0 ([]) in
    let r = predicate "r" 0 ([]) in
    NonSelected(empty, singleton(implies (implies p (implies q r)) (implies (implies p q) (implies p r))));;

  let stage1_ex6 =
    let p = predicate "p" 0 ([]) in
    let q = predicate "q" 0 ([]) in
    NonSelected(empty, singleton(implies (implies (_and p q) _false) (_or (implies p _false) (implies q _false))))

  let stage1_ex7 =
    let p1 = predicate "p1" 0 ([]) in
    let p2 = predicate "p2" 0 ([]) in
    let q1 = predicate "q1" 0 ([]) in
    let q2 = predicate "q2" 0 ([]) in
    NonSelected(empty, singleton(implies (_or (_and p1 q1) (_and p2 q2)) (_and (_or p1 q2) (_or q1 q2))));;

  let stage2_ex1 =
    let x = variable "x" in
    let y = variable "y" in
    let p = predicate "p" 2 (x::y::[]) in
    NonSelected(empty, singleton (implies (exists "x" (forall "y" p)) (forall "y" (exists "x" p))));;

  let stage2_ex2 =
    let x = variable "x" in
    let p = predicate "p" 1 (x::[]) in
    NonSelected(empty, singleton (implies (forall "x" (implies (implies p _false) _false)) (implies (implies (forall "x" p) _false) _false)));;

  let stage2_ex3 =
    let x = variable "x" in
    let y = variable "y" in
    let p = predicate "p" 1 (x::[]) in
    let q = predicate "p" 1 (y::[]) in
    NonSelected(empty, singleton (exists "x" (implies p (forall "y" q))));;

  let stage2_ex4 =
    let a = constant "a" in
    let b = constant "b" in
    let x = variable "x" in
    let y = variable "y" in
    let abab = predicate "pos" 4 (a::b::a::b::[]) in
    let bbab = predicate "pos" 4 (b::b::a::b::[]) in
    let baba = predicate "pos" 4 (b::a::b::a::[]) in
    let aaba = predicate "pos" 4 (a::a::b::a::[]) in
    let aaab = predicate "pos" 4 (a::a::a::b::[]) in
    let bbab = predicate "pos" 4 (b::b::a::b::[]) in
    let bbba = predicate "pos" 4 (b::b::b::a::[]) in
    let aaba = predicate "pos" 4 (a::a::b::a::[]) in
    let abaa = predicate "pos" 4 (a::b::a::a::[]) in
    let babb = predicate "pos" 4 (b::a::b::b::[]) in
    let axay = predicate "pos" 4 (a::x::a::y::[]) in
    let bxby = predicate "pos" 4 (b::x::b::y::[]) in
    let aaaa =predicate "pos" 4 (a::a::a::a::[]) in
    let bbbb = predicate "pos" 4 (b::b::b::b::[]) in
    let i1 = implies abab bbab in
    let i2 = implies bbab abab in
    let i3 = implies baba aaba in
    let i4 = implies aaba baba in
    let i5 = implies aaab bbab in
    let i6 = implies bbab aaab in
    let i7 = implies bbba aaba in
    let i8 = implies aaba bbba in
    let i9 = implies abaa bbab in
    let i10 = implies bbab abaa in
    let i11 = implies babb aaba in
    let i12 = implies aaba babb in
    let i13 = forall "x" (forall "y" (implies axay bxby)) in
    let i14 = forall "x" (forall "y" (implies bxby axay)) in
    let f = List.fold_left (fun s f -> add f s) empty (i1::i2::i3::i4::i5::i6::i7::i8::i9::i10::i11
                                                  ::i12::i13::i14::[]) in
    NonSelected(add aaaa f, singleton bbbb);;

  let all_ex =
    stage1_ex1::stage1_ex2::stage1_ex3::stage1_ex4::stage1_ex5::stage1_ex6::stage1_ex7::stage2_ex1::stage2_ex2::stage2_ex3::stage2_ex4::[];;
end;;
