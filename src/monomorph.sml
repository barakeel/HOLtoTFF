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

(* all variables *)
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

(*
val substll = [[1,2,3],[4,5],[6]];
val instl = [];
*)

(* constants *)
(* tools *)
fun inv f a b = f b a

fun empty_inter l1 l2 =
  case l1 of
    [] => true
  | a :: m => (not (is_member a l2)) andalso empty_inter m l2 
  
fun get_redexl subst =
  case subst of
    [] => [] 
  | {redex = red, residue = res} :: m => red :: get_redexl m 
  
fun disjunct_redexl subst1 subst2 =
  empty_inter (get_redexl subst1) (get_redexl subst2)
    
fun add_subst subst1 subst2 =
  if disjunct_redexl subst1 subst2 
  then subst1 @ subst2
  else subst1
  
fun multone_subst subst substl =
  case substl of
    [] => []
  | [s] => [add_subst subst s] 
  | s :: m => add_subst subst s :: multone_subst subst m
   
fun mult_subst substl1 substl2 =  
  case substl1 of
    [] => []
  | [s1] => multone_subst s1 substl2
  | s1 :: m => (multone_subst s1 substl2) @ (mult_subst m substl2)
  
fun list_mult_subst_aux substll =
  case substll of  
    [] => []
  | [s] => s
  | s :: m =>  mult_subst (list_mult_subst_aux m) s
  
fun list_mult_subst l = list_mult_subst_aux (rev l)

(* *)
fun create_substl_c const cl =
  case cl of
    [] => [[]]
  | c :: m => if name_of const = name_of c 
              then match_type (type_of const) (type_of c) :: 
                   create_substl_c const m 
              else create_substl_c const m
 
fun create_substl_c_goal c goal =
  create_substl_c c (get_cl_goal goal)
 
fun create_substl_cl_goal cl goal =
  let val substll = map (inv create_substl_c_goal goal) cl in
    list_mult_subst substll
  end 

fun create_substl_thm_goal_c thm goal =
  let val cl = get_cl_thm thm in
    create_substl_cl_goal cl goal
  end

(* monomorphisation *)
fun same_ccl th1 th2 = aconv (concl th1) (concl th2)
fun erase_double_ccl thml = erase_double_eq same_ccl thml
  
  
fun monomorph substl thm  = 
  let val thml = erase_double_ccl (map (inv INST_TYPE thm) substl) in
    if null thml then raise MONOMORPH_ERR "monomorph" ""
    else LIST_CONJ thml
  end

(* constant monomorphisation *)
fun monomorph_c thm goal =
  let val substl = create_substl_thm_goal_c thm goal in
    monomorph substl thm
  end

fun monomorph_pb_c thml goal = map (inv monomorph_c goal) thml
   



(* test   
 val th1 = ASSUME ``!x. x=x`` ;
 val th2 = ASSUME ``!y. y=y`` ;
 LIST_CONJ [th1,th2];
 
 show_assums := true;
val term = ``(z = y) /\ (x = 0)``;
val goal = ([term],F); 
val thm1 = mk_thm ([``(x = y)``],F); 
val thm2 = ASSUME ``x=0``;
val thml = [thm1,thm2];
*)


end

           