structure monomorph :> monomorph =
struct

(*
load "listtools"; open listtools;
load "mydatatype"; open mydatatype;
load "tools"; open tools;

load "extractvar"; open extractvar;
load "namevar"; open namevar;
*)
open HolKernel Abbrev numSyntax 
     listtools mydatatype tools
     extractvar namevar


fun MONOMORPH_ERR function message =
    HOL_ERR{origin_structure = "monomorph",
            origin_function = function,
            message = message}


(* If I want to monomorph a term *)
(* should only monomorph once *)
(* monomorph to its own type *)
(* returns a list of substitution *)
fun mk_multielem tyl varty = (varty,tyl)
fun mk_multisubst vartyl tyl = map (mk_multielem tyl) vartyl

fun mk_elem (red,res) = {redex = red, residue = res}
fun add_elem elem subst = elem :: subst
(* return a list of substitution *)
fun add_eleml elem substl = map (add_elem elem) substl

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
  let val vartyl = filter is_vartype tyl in
  let val multisubst = mk_multisubst vartyl tyl in
    add_multisubst multisubst []  
  end end end
        

(* test   
val term = ``x = y``;
 *)  
type_of term;

end

           