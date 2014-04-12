structure blibExtract :> blibExtract =
struct

open HolKernel Abbrev boolLib blibTools 
(* Extract variables *)
datatype VARSORT = Bvar | Fvar | Cvar

fun info_var term bvl =
  if is_var term then 
    if mem term bvl then [((term,0),Bvar)] else [((term,0),Fvar)]
  else if is_const term then 
    if term = T orelse term = F then []
    else [((term,0),Cvar)]
  else if is_binop term orelse is_eq term 
       then info_var (lhand term) bvl @ info_var (rand term) bvl
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
      if mem oper bvl then ((oper,n),Bvar) :: l else ((oper,n),Fvar) :: l
    else if is_const oper then ((oper,n),Cvar) :: l
    else if is_abs oper then 
      let val (abvl,t) = strip_abs oper in info_var_abs abvl t bvl @ l end  
    else raise B_ERR "info_var" "comb" 
  end end

(* test
val term = ``(\x. (z = 2))``;
*)
fun info_varl term = mk_set (info_var term [])
(* return a list of triple (variable,number of arguments,structure) *)

fun is_bv (a,b) = (b = Bvar)
fun is_fv (a,b) = (b = Fvar)
fun is_c (a,b) = (b = Cvar)
fun is_fvc (a,b) = (b = Fvar) orelse (b = Cvar)

fun get_bval term = map fst (filter is_bv (info_varl term))
fun get_fval term = map fst (filter is_fv (info_varl term))
fun get_cal term = map fst (filter is_c (info_varl term))
fun get_fvcal term = map fst (filter is_fvc (info_varl term))  

fun get_bvl term = map fst (get_bval term)
fun get_cl term = map fst (get_cal term)
fun get_fvcl term = map fst (get_fvcal term)
fun get_cl_thm thm = merge (map get_cl (concl thm :: hyp thm))

(* Extract types *)
fun all_tya term = 
  let val varal = (map fst (info_varl term)) in
    mk_set (map (fst_f type_of) varal)
  end
  
fun is_sty (ty,arity) = (arity = 0)
fun get_styal term = filter is_sty (all_tya term)

fun is_cty (ty,arity) = (arity > 0)
fun get_ctyal term  = filter is_cty (all_tya term)


fun strip_type_n (ty,a) = 
  if a = 0 then ([],(ty,0))
  else if a > 0 then
    let val (str,l) = gen_dest_type ty in
    let val (ty1,ty2) = (List.nth (l,0),List.nth (l,1)) in
    let val resl = strip_type_n (ty2,(a-1)) in
    let val (argl,im) = (fst resl,snd resl) in
      ((ty1,0) :: argl,im) 
    end end end end
  else raise B_ERR "strip_type_n" "negative"

fun flatten_ctya ctya = 
  let val (argl,im) = strip_type_n ctya in im :: argl end
fun flatten_ctyal ctyal = merge (map flatten_ctya ctyal)

fun get_tyal term = merge (map flatten_ctya (get_ctyal term @ get_styal term))

end 