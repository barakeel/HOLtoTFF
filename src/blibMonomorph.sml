structure blibMonomorph :> blibMonomorph =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype
     blibSyntax
     blibExtractvar blibNamevar
     beagleStats

fun MONOMORPH_ERR function message =
    HOL_ERR{origin_structure = "blibMonomorph",
            origin_function = function,
            message = message}


(* TEST *)
fun is_polymorph term = (polymorphic o type_of) term
fun is_polymorph_thm thm = 
  exists is_polymorph (get_cl_thm thm)
fun is_polymorph_pb (thml,goal) = exists is_polymorph_thm thml

fun is_monomorphable c = is_polymorph c andalso not (name_of c = "=") 


(* SUBSTITION SET *)
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
  
(* SUBSTITUTION NORMALISATION *)
fun less_ty (ty1,ty2) = (Type.compare (ty1,ty2) = LESS)
  
fun less_redres ({redex = r1, residue = _},{redex = r2, residue = _}) =
  less_ty (r1,r2)
    
fun normalize_subst subst =
  quicksort less_redres (erase_double subst)
  
fun normalize_substl substl =
  erase_double (map normalize_subst substl)
  
(* SUBSTITUTION ARITHMETIC *)
(* every entry is normalized and should return normalized *)
fun merge_subst subst1 subst2 =
  let val l1 = get_redl subst1 in
  let val l2 = get_redl subst2 in
  let val l3 = inter l1 l2 in
  let val subst1aux = repeat_change remove_red l3 subst1 in
    normalize_subst (subst1aux @ subst2)
  end end end end  

fun add_subst subst1 subst2 =
  if compatible_subst subst1 subst2 
  then normalize_substl [subst1,subst2,merge_subst subst1 subst2]
  else normalize_substl [subst1,subst2]
  
fun multone_subst_aux subst substl =
  case substl of
    [] => []
  | s :: m => normalize_substl (add_subst subst s @ multone_subst_aux subst m)

fun multone_subst subst substl = 
  wrap "blibMonomorph" "multone_subst" "" (multone_subst_aux subst) substl  
   
fun mult_subst substl1 substl2 =  
  case substl1 of
    [] => []
  | s1 :: m => normalize_substl (
               (multone_subst s1 substl2) @ (mult_subst m substl2)
               )
  
fun list_mult_subst_aux substll =
  case substll of  
    [] => []
  | [sl] => sl
  | sl :: m => normalize_substl (mult_subst (list_mult_subst_aux m) sl)

fun list_mult_subst l = 
  wrap "blibMonomorph" "list_mult_subst" "" list_mult_subst_aux (rev l)

(* SUBSTL MAXIMAL ELEMENTS *)
fun is_identity {redex = red, residue = res} = (red = res)

fun remove_identity s = filter (not o is_identity) s 

fun get_maxsubstl sl = 
   erase_double ( map (remove_identity)  
      (filter (inv is_maxset sl) sl)) 

(* MATCH *)
fun mk_identity vty = {redex = vty, residue = vty}

fun raw_subst (subst,vtyl) = normalize_subst (subst @ map mk_identity vtyl)

fun is_matchable c1 c2 =
  name_of c1 = name_of c2 andalso 
  success (match_type (type_of c1)) (type_of c2)

fun match_c_c c1 c2 = raw_subst (raw_match_type (type_of c1) (type_of c2) ([],[]))

(* may return an empty list *)
fun match_c_cl c cl =
  let val newcl = filter (is_matchable c) cl in
    map (match_c_c c) newcl
  end
 
(* INSTANTIATION *) 
fun inst_cl_aux substl cl = 
  case substl of 
    [] => []
  | s :: m => map (Term.inst s) cl :: inst_cl_aux m cl

fun inst_cl substl cl = 
  let val newsubstl = erase_double ([] :: substl) in
    wrap "blibMonomorph" "inst_cl" "" merge (inst_cl_aux newsubstl cl)
  end
  
fun inst_cll substll clthml =
  if not (length substll = length clthml)
  then 
    raise MONOMORPH_ERR "inst_cll" "list of different length" 
  else
    case clthml of
        [] => []
      | _  => inst_cl (hd substll) (hd clthml) :: 
              inst_cll (tl substll) (tl clthml)
              
fun inst_thm substl thm  = 
  let val newsubstl = erase_double ([] :: substl) in
    LIST_CONJ (map (inv INST_TYPE thm) newsubstl)
  end

fun inst_thml substll thml =
  if not (length substll = length thml) 
  then 
    raise MONOMORPH_ERR "inst_thml" "list of different length" 
  else
    case thml of
        [] => []
      | _  => inst_thm (hd substll) (hd thml) :: 
              inst_thml (tl substll) (tl thml)

(* SUBSTITUTION CREATION FROM A PROBLEM *) 
fun create_substl clthm clpb =
  let val mclthm = filter is_monomorphable clthm in
  let val substll1 = map (inv match_c_cl clpb) mclthm in
  let val substll2 = map (normalize_substl) substll1 in
  let val substll3 = filter (not o null) substll2 in
    list_mult_subst substll3
  end end end end 

fun create_substll clthml clpb = map (inv create_substl clpb) clthml

(* main loop of the monomorphisation *)
fun repeat_create_substll (clthml,clgoal) substll =
  let val clpb = merge (clthml @ [clgoal]) in
  let val newsubstll = create_substll clthml clpb in
  let val n = suml (map length substll) in
  let val newn = suml (map length newsubstll) in
  let val maxn = suml (map length (map get_maxsubstl newsubstll)) in
    (
    if newn <= n then flag_on fixpflag else ()
    ;
    if newn <= n orelse maxn > 15
    then 
      map get_maxsubstl substll
    else 
      repeat_create_substll (inst_cll newsubstll clthml,clgoal) newsubstll
    )
  end end end end end 

(* main function *)  
fun monomorph_pb_w (thml,goal) =
  let val clthml = map get_cl_thm thml in
  let val clgoal = get_cl_goal goal in
  let val substll = repeat_create_substll 
                     (clthml,clgoal) 
                     (mk_list (length thml) [[]])                    
  in
    (inst_thml substll thml,goal) 
  end end end
fun monomorph_pb pb = 
  wrap "blibMonomorph" "monomorph_pb" "" monomorph_pb_w pb

end

           