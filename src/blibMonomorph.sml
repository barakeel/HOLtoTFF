structure blibMonomorph :> blibMonomorph =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype
     blibSyntax
     blibExtractvar blibNamevar

fun MONOMORPH_ERR function message =
    HOL_ERR{origin_structure = "blibMonomorph",
            origin_function = function,
            message = message}

(* TEST *)
fun is_polymorph term = (polymorphic o type_of) term
fun is_polymorph_thm thm =  exists is_polymorph (get_cl_thm thm)
fun is_polymorph_pb (thml,goal) = exists is_polymorph_thm thml

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

fun get_max_substl sl = 
   erase_double ( map (remove_identity)  
      (filter (inv is_maxset sl) sl)) 

(* INSTANTIATION *) 
fun inst_cl_aux substl cl = 
  case substl of 
    [] => []
  | s :: m => map (Term.inst s) cl @ inst_cl_aux m cl

fun inst_cl substl cl = 
    wrap "blibMonomorph" "inst_cl" "" erase_double (inst_cl_aux substl cl)
  
fun inst_thm substl thm  = 
  if null substl then raise MONOMORPH_ERR "inst_thm" "" 
  else LIST_CONJ (map (inv INST_TYPE thm) substl)

fun inst_thml substll thml =
  if not (length substll = length thml) 
  then 
    raise MONOMORPH_ERR "inst_thml" "list of different length" 
  else
    case thml of
        [] => []
      | _  => inst_thm (hd substll) (hd thml) :: 
              inst_thml (tl substll) (tl thml)


(* Substitution creation from constants *)
fun mk_identity vty = {redex = vty, residue = vty}

fun raw_subst (subst,vtyl) = (subst @ map mk_identity vtyl)

fun is_matchable c1 c2 =
  namev_of c1 = namev_of c2 andalso success (match_type (type_of c1)) (type_of c2)

fun match_c_c c1 c2 = 
  normalize_subst (raw_subst (raw_match_type (type_of c1) (type_of c2) ([],[])))

fun match_c_cl c cl =
  let val newcl = filter (is_matchable c) cl in
    map (match_c_c c) newcl
  end

fun match_pcl_thm pcl cl = map (inv match_c_cl cl) pcl
    
(* Constants creation *)
fun infer_newcl_thm pcl cl =
  let val substll = match_pcl_thm pcl cl in
  let val substl = merge substll in
  let val newcl = inst_cl substl pcl in
    newcl
  end end end
  
fun infer_newcl_thml pcll cl = merge (map (inv infer_newcl_thm cl) pcll)

(* Substitutions creation *)
(* creation of a list of substitution for a theorem in a problem *) 
fun create_substl pcl cl =
  let val substll1 = match_pcl_thm pcl cl in
    get_max_substl (list_mult_subst substll1)
  end

fun create_substll pcll cl = map (inv create_substl cl) pcll


(* Main function *) 
(* loop *)
fun monomorph_pb_loop pcll cl1 =
  let val cl2 = erase_double (cl1 @ (infer_newcl_thml pcll cl1)) in
    if length cl1 = length cl2 then create_substll pcll cl1 
    else
      let val substll2 = create_substll pcll cl2 in
      let val n2 = suml (map length substll2) in
        if n2 <= 15 then monomorph_pb_loop pcll cl2
        else create_substll pcll cl1 
      end end
  end

fun monomorph_pb_w (thml,goal) =
  let val pthml = filter is_polymorph_thm thml in
  let val npthml = filter (not o is_polymorph_thm) thml in
  let val pcll =  map ((filter is_polymorph) o get_cl_thm) pthml in
  let val cl = merge (get_cl_goal goal :: map get_cl_thm thml) in
  let val substll = monomorph_pb_loop pcll cl in 
    (npthml @ inst_thml substll pthml,goal) 
  end end end end end

fun monomorph_pb pb = wrap "blibMonomorph" "monomorph_pb" "" monomorph_pb_w pb


end

           