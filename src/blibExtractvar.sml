structure blibExtractvar :> blibExtractvar =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype blibSyntax blibTffsyntax

fun EXTRACTVAR_ERR function message =
  HOL_ERR{origin_structure = "blibExtractvar",
          origin_function = function,
          message = message}

fun info_var term bvl =
  case structterm term of
    Numeral => []
  | Integer => []
  | Var => if is_member term bvl
           then [((term,0),Boundvar)] 
           else [((term,0),Freevar)]
  | Const => (
             case structleafc term of
               True => []
             | False => []
             | _ => [((term,0),Constvar)]
             )
  | Comb => 
    ( 
    (* hack NLIA *)
    case structcomb term of
      Multn => if linearn term then info_var_binop term bvl
                               else info_var_app term bvl
    | Multi => if lineari term then info_var_binop term bvl
                               else info_var_app term bvl
    | _ =>
    (
    (* end hack NLIA *)
    case structarity term of
      Binop => info_var_binop term bvl
    | Unop => info_var_unop term bvl
    | Quant => let val (qbvl,t) = strip_quant term in
                  info_var_abs qbvl t bvl
                end       
    | _ => info_var_app term bvl
      
    ))         
    | Abs => let val (absbvl,t) = strip_abs term in
               info_var_abs absbvl t bvl 
             end  
and info_var_l terml bvl = 
  case terml of
    [] => [] 
  | t :: m => (info_var t bvl) @ (info_var_l m bvl)
and info_var_unop term bvl =
  let val (oper,l) = strip_comb term in
  let val lhs = hd l in
    info_var lhs bvl
  end end
and info_var_binop term bvl = 
  let val (oper,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in
    (info_var lhs bvl) @ (info_var rhs bvl) 
  end end
and info_var_abs bvl1 term bvl2 = 
  (info_var_l bvl1 (bvl1 @ bvl2)) @ (info_var term (bvl1 @ bvl2))
and info_var_app term bvl =
  let val (oper,argl) = strip_comb term in
  let 
    val n = length argl 
    val l = info_var_l argl bvl 
  in
    case structterm oper of
      Numeral => raise EXTRACTVAR_ERR "info_var_" "oper is num"
    | Integer => raise EXTRACTVAR_ERR "info_var_" "oper is int"
    | Var =>  if is_member oper bvl
              then ((oper,n),Boundvar) :: l
              else ((oper,n),Freevar) :: l
    | Const => ((oper,n),Constvar) :: l
    | Comb => raise EXTRACTVAR_ERR "info_var_" "oper is comb"
    | Abs => let val (absbvl,t) = strip_abs oper in
               info_var_abs absbvl t bvl @ l
             end  
  end end

fun info_varl term = erase_double (info_var term [])
fun list_info_varl terml = erase_double (info_var_l terml [])
(* return a list of triple (variable,number of arguments,structure) *)


fun is_in_bval (a,b) = (b = Boundvar)
fun is_in_fval (a,b) = (b = Freevar)
fun is_in_cal (a,b) = (b = Constvar)
fun is_in_fvcal (a,b) = (b = Freevar) orelse (b = Constvar)

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