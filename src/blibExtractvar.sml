structure blibExtractvar :> blibExtractvar =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype blibSyntax blibTffsyntax

datatype VARSORT = Bvar | Fvar | Cvar

fun info_var term bvl =
  if is_var term then 
    if is_member term bvl then [((term,0),Bvar)] else [((term,0),Fvar)]
  else if is_const term then 
    if term = T orelse term = F then []
    else [((term,0),Cvar)]
  else if is_binop term then info_var (lhand term) bvl @ info_var (rand term) bvl
  else if is_unop term then info_var (rand term) bvl
  else if is_quant term then 
    let val (qbvl,t) = strip_quant term in info_var_abs qbvl t bvl end       
  else if is_abs term then 
    let val (absbvl,t) = strip_abs term in info_var_abs absbvl t bvl end
  else info_var_app term bvl
and info_var_l terml bvl = 
  case terml of
    [] => [] 
  | t :: m => info_var t bvl @ info_var_l m bvl
and info_var_abs bvl1 term bvl2 = 
  info_var_l bvl1 (bvl1 @ bvl2) @ info_var term (bvl1 @ bvl2)
and info_var_app term bvl =
  let val (oper,argl) = strip_comb term in
  let 
    val n = length argl 
    val l = info_var_l argl bvl 
  in
    if is_var oper then 
      if is_member oper bvl then ((oper,n),Bvar) :: l else ((oper,n),Fvar) :: l
    else if is_const oper then ((oper,n),Cvar) :: l
    else if is_abs oper then 
      let val (abvl,t) = strip_abs oper in info_var_abs abvl t bvl @ l end  
    else raise B_ERR "info_var" "comb" 
  end end

(* test
val term = ``(\x. (z = 2))``;
*)
fun info_varl term = erase_double (info_var term [])
(* return a list of triple (variable,number of arguments,structure) *)

fun is_in_bval (a,b) = (b = Bvar)
fun is_in_fval (a,b) = (b = Fvar)
fun is_in_cal (a,b) = (b = Cvar)
fun is_in_fvcal (a,b) = (b = Fvar) orelse (b = Cvar)

fun get_bval term = map fst (filter is_in_bval (info_varl term))
fun get_fval term = map fst (filter is_in_fval (info_varl term))
fun get_cal term = map fst (filter is_in_cal (info_varl term))
fun get_fvcal term = map fst (filter is_in_fvcal (info_varl term))  

fun get_bvl term = map fst (get_bval term)
fun get_fvl term = map fst (get_fval term)
fun get_cl term = map fst (get_cal term)
fun get_fvcl term = map fst (get_fvcal term)
fun all_var term = map fst (map fst (info_varl term))
fun all_vara term = map fst (info_varl term)
fun all_varl terml = merge (map all_var terml)

fun concat_thm return_list thm =
  let val l = (hyp thm) @ [concl thm] in
    merge (map return_list l)
  end 
  
fun get_fvl_thm thm = concat_thm get_fvl thm
fun get_bvl_thm thm = concat_thm get_bvl thm
fun get_cl_thm thm = concat_thm get_cl thm
fun get_fvcl_thm thm = concat_thm get_fvcl thm
fun all_var_thm thm = concat_thm all_var thm
fun all_vara_thm thm = concat_thm all_vara thm

fun concat_goal returnalist goal =
  let val l = fst goal @ [snd goal] in
    merge (map returnalist l)
  end
  
fun get_fvl_goal goal = concat_goal get_fvl goal
fun get_bvl_goal goal = concat_goal get_bvl goal
fun get_cl_goal goal = concat_goal get_cl goal
fun get_fvcl_goal goal = concat_goal get_fvcl goal
fun all_var_goal goal = concat_goal all_var goal
fun all_vara_goal goal = concat_goal all_vara goal

end 