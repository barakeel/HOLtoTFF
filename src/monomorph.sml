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

fun add_eleml elem substl = 
  case substl of
    [] => [[elem]]
  | _ => map (add_elem elem) substl

fun add_multielem multielem substl = 
  case multielem of
    (varty,[]) => substl
  | (varty,ty :: m) => 
    let val elem = mk_elem (varty,ty) in  
      (add_eleml elem substl) @ (add_multielem (varty,m) substl) 
    end

fun add_multisubst multisubst substl =
  repeatchange add_multielem multisubst substl

fun all_subst vartyl tyl =
  let val multisubst = mk_multisubst vartyl tyl in
    add_multisubst multisubst []  
  end 

fun all_subtype_goal goal = 
  erase_double (List.concat (
    all_subtype (snd goal) :: map all_subtype (fst goal)
    ))

fun all_vartype_thm thm = 
  erase_double (List.concat (
    all_vartype (concl thm) :: map all_vartype (hyp thm)
    ))

fun all_subst_thm thm goal =
  let val vartyl = all_vartype_thm thm in
  let val tyl = all_subtype_goal goal in
  let val substl = all_subst vartyl tyl in
    if substl = [] then [[]] else substl (* add the empty subst *)
  end end end

fun all_subst_thm_rev goal thm = all_subst_thm thm goal  
fun list_all_subst_thm thml goal = map (all_subst_thm_rev goal) thml

(* just to explode *)
fun prepend subst inst = subst :: inst 
fun prepend_all elem instl = 
  if null instl then [[elem]]
  else map (prepend elem) instl
 
fun prepend_all_rev instl subst = prepend_all subst instl

fun list_prepend_all substl instl = 
  List.concat (map (prepend_all_rev instl) substl)

fun mk_instl_aux substll instl = repeatchange list_prepend_all substll instl
fun mk_instl substll = mk_instl_aux (rev substll) [] 

(*
val substll = [[1,2,3],[4,5],[6]];
val instl = [];
*)
fun monomorph thm subst = INST_TYPE subst thm

fun list_monomorph thml inst =
  case thml of
    [] => []
  | thm :: m => monomorph thm (hd inst) :: list_monomorph m (tl inst)
  
fun monomorph_rule thml goal =
  let val substll = list_all_subst_thm thml goal in
  let val instl = mk_instl substll in
  let val newthmll = map (list_monomorph thml) instl in
  let val newthml = map (LIST_CONJ o (map DISCH_ALL)) newthmll in
    newthml
  end end end end
    handle _ => raise MONOMORPH_ERR "monomorph_rule" ""
(* test   
show_assums := true;
val term = ``(z = y) /\ (x = 0)``;
val goal = ([term],F); 
val thm1 = mk_thm ([``(x = y)``],F); 
val thm2 = ASSUME ``x=0``;
val thml = [thm1,thm2];
*)


end

           