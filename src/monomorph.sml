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


(* TOOLS *)
fun get_redl subst =
  case subst of
    [] => [] 
  | {redex = red, residue = res} :: m => red :: get_redl m 
  
fun red_to_res red subst =
  case subst of
    [] => raise MONOMORPH_ERR "image_subst" "redex not found"  
  | {redex = red1, residue = res1} :: m => 
    if red = red1 then res1 else red_to_res red m
 
fun remove_red red subst =
  case subst of
    [] => []
  | {redex = red1, residue = res1} :: m => 
    if red = red1 
    then remove_red red m 
    else {redex = red1, residue = res1} :: remove_red red m 

fun same_res subst1 subst2 red  = 
  red_to_res red subst1 = red_to_res red subst2
   
fun compatible_subst subst1 subst2 =
  let val l1 = get_redl subst1 in
  let val l2 = get_redl subst2 in
  let val l3 = inter l1 l2 in
    all (same_res subst1 subst2) l3 
  end end end

(* ARITHMETIC FOR SUBSTITUTION *)
fun merge_subst subst1 subst2 =
  let val l1 = get_redl subst1 in
  let val l2 = get_redl subst2 in
  let val l3 = inter l1 l2 in
  let val subst1aux = repeatchange remove_red l3 subst1 in
    subst1aux @ subst2
  end end end end  
    
fun add_subst subst1 subst2 =
  if compatible_subst subst1 subst2 
  then [merge_subst subst1 subst2]
  else [subst1,subst2]
  
fun multone_subst subst substl =
  case substl of
    [] => [[]]
  | [s] => add_subst subst s
  | s :: m => add_subst subst s @ multone_subst subst m
   
fun mult_subst substl1 substl2 =  
  case substl1 of
    [] => [[]]
  | [s1] => multone_subst s1 substl2
  | s1 :: m => (multone_subst s1 substl2) @ (mult_subst m substl2)
  
fun list_mult_subst_aux substll =
  case substll of  
    [] => [[]]
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

(* SUBSTITUTION NORMALISATION *)
fun is_identity {redex = red, residue = res} = (red = res)
fun erase_identity subst = filter (not o is_identity) subst

fun less_ty (ty1,ty2) = 
  case Type.compare (ty1,ty2) of
    LESS => true
  | EQUAL => false
  | GREATER => false
  
fun less_redres ({redex = r1, residue = _},{redex = r2, residue = _}) =
  less_ty (r1,r2)
    
fun normalize_subst subst =
  quicksort less_redres (erase_identity subst)
  
fun normalize_substl substl =
  erase_double (map normalize_subst substl)

(* INSTANTIATION *) 
fun inst_thm substl thm  = 
  let val newsubstl = normalize_substl substl in
  let val thml = (map (inv INST_TYPE thm) newsubstl) in
    if null thml 
    then raise MONOMORPH_ERR "monomorph" ""
    else LIST_CONJ thml
  end end

(* MONOMORPHISATION *)   
  (* preparation *)
fun create_substl_thm_pb thm (thml,goal) = 
  let val cl1 = filter (polymorphic o type_of) (get_cl_thm thm) in
  let val cl2 = erase_double 
    (List.concat ((get_cl_goal goal) :: (map get_cl_thm thml)))
  in 
    create_substl_cl_cl cl1 cl2
  end end

fun monomorph_thm_pb_w thm pb =
  let val substl = create_substl_thm_pb thm pb in
    inst_thm substl thm
  end  
fun monomorph_thm_pb thm pb = 
  wrap "monomorph" "monomorph_thm_pb" (thm_to_string thm) 
    (monomorph_thm_pb_w thm) pb
  
  (* *)
fun monomorph_pb_w (thml,goal) =
  (map (inv monomorph_thm_pb (thml,goal)) thml,goal)  
fun monomorph_pb pb = wrap "monomorph" "monomorph_pb" "" monomorph_pb_w pb

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

           