structure monomorph :> monomorph =
struct

(*
load "listtools"; open listtools;
load "mydatatype"; open mydatatype;
load "tools"; open tools;

load "extractvar"; open extractvar;
load "namevar"; open namevar;
*)
open HolKernel Abbrev boolLib numSyntax 
     listtools mydatatype tools
     extractvar namevar

fun MONOMORPH_ERR function message =
    HOL_ERR{origin_structure = "monomorph",
            origin_function = function,
            message = message}

fun mk_multielem tyl varty = (varty,tyl)
fun mk_multisubst vartyl tyl = map (mk_multielem tyl) vartyl

fun mk_elem (red,res) = {redex = red, residue = res}
fun add_elem elem subst = elem :: subst
(* return a list of substitution *)
fun add_eleml elem substl = 
  case substl of
    [] => [[elem]]
  | _ => map (add_elem elem) substl

(* assuming it's a new multielem *)
(* return a list of substitution *)
fun add_multielem multielem substl = 
  case multielem of
    (varty,[]) => substl
  | (varty,ty :: m) => 
    let val elem = mk_elem (varty,ty) in  
      (add_eleml elem substl) @ (add_multielem (varty,m) substl) 
    end

fun add_multisubst multisubst substl =
  repeatchange add_multielem multisubst substl

fun all_subst term =
  let val tyl = all_type term in
  let val vartyl = all_vartype term in
  let val multisubst = mk_multisubst vartyl tyl in
    add_multisubst multisubst []  
  end end end


(* term should have type bool *) (* no proof *)
fun INST_TYPE_rev a b = INST_TYPE b a

(* goal has the form ([term],F) thm has form ([CONJ term list],F) *)


(*
remove vartype when you instantiate
but you can do pre_monomorphisation

x:int = y:int |- F

x:'a = y:'a |- F
'a -> 'b
'b -> 'a


*)

(* try with first monomorphisation *)
(* try with second monomorphisation *)

(* I should monomorph before doing anything else *)


(* test   
val term = ``(z = y) /\ (x = 0)``;
val goal = ([term],F); 
val thm = mk_thm ([monomorph term],F); 
all_subst term;
monomorph term;
all_vartype term;
all_type term;
 show_assums := true;
 
 
 x = y alpha
 <=> !type x:ty = y:ty
 *)
 

end

           