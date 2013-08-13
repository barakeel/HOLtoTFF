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

(* create a list of substitution *)
fun is_matchable c1 c2 =
  name_of c1 = name_of c2 andalso 
  success (match_type (type_of c1)) (type_of c2)
        
fun create_substl_c const cl =
  case cl of
    [] => [[]]
  | c :: m => 
    if is_matchable const c
    then match_type (type_of const) (type_of c) :: 
         create_substl_c const m 
    else create_substl_c const m
 
fun create_substl_cl_cl cl1 cl2 = 
  list_mult_subst (map (inv create_substl_c cl2) cl1)

(* INSTANTIATION *)
fun same_ccl th1 th2 = aconv (concl th1) (concl th2)
fun erase_double_ccl thml = erase_double_eq same_ccl thml
  
fun inst_thm substl thm  = 
  let val thml = erase_double_ccl (map (inv INST_TYPE thm) substl) in
    if null thml then raise MONOMORPH_ERR "monomorph" ""
    else LIST_CONJ thml
  end

(* MONOMORPHISATION *)   
  (* preparation *)
fun create_substl_thm_pb thm (thml,goal) = 
  let val cl1 = get_cl_thm thm in
  let val cl2 = erase_double (List.concat 
                  ((get_cl_goal goal) :: (map get_cl_thm thml)))
  in 
    create_substl_cl_cl cl1 cl2
  end end

fun monomorph_thm_pb thm pb =
  let val substl = create_substl_thm_pb thm pb in
    inst_thm substl thm
  end  
  (* *)
fun monomorph_pb_w (thml,goal) =
  (map (inv monomorph_thm_pb (thml,goal)) thml,goal)  
fun monomorph_pb pb = wrap "monomorph" "monomorph_pb" "" monomorph_pb_w pb

fun monomorph_n_pb n pb = repeat_n_fun n monomorph_pb pb

(* TEST *)
fun is_polymorph term = not (null (all_vartype term)) 
fun is_polymorph_thm thm = exists is_polymorph (get_cl_thm thm)
fun is_polymorph_pb (thml,goal) = exists is_polymorph_thm thml

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

           