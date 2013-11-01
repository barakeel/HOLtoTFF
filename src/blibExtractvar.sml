structure blibExtractvar :> blibExtractvar =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype

fun EXTRACTVAR_ERR function message =
  HOL_ERR{origin_structure = "blibExtractvar",
          origin_function = function,
          message = message}

fun get_var term bvl =
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
             | Otherleafc => [((term,0),Constvar)]
             )
  | Comb => 
    ( 
    (* hack NLIA *)
    if 
    then
    else
    
    
    
    (* end hack NLIA *)
    case structcomb term of
      Binop => get_varbinop term bvl
    | Unop => get_varunop term bvl
    | Quant => let val (qbvl,t) = strip_quant term in
                  get_varabs qbvl t bvl
                end       
    | _ =>  
      let val (oper,argl) = strip_comb term in
      let 
        val n = length argl 
        val l = get_varl argl bvl 
      in
        case structterm oper of
          Numeral => raise EXTRACTVAR_ERR "get_var" "oper is num"
        | Integer => raise EXTRACTVAR_ERR "get_var" "oper is int"
        | Var =>  if is_member oper bvl
                  then ((oper,n),Boundvar) :: l
                  else ((oper,n),Freevar) :: l
        | Const => ((oper,n),Constvar) :: l
        | Comb => raise EXTRACTVAR_ERR "get_var" "oper is comb"
        | Abs => let val (absbvl,t) = strip_abs oper in
                   get_varabs absbvl t bvl @ l
                 end  
      end end
    )         
    | Abs => let val (absbvl,t) = strip_abs term in
               get_varabs absbvl t bvl 
             end  
and get_varl terml bvl = 
  case terml of
    [] => [] 
  | t :: m => (get_var t bvl) @ (get_varl m bvl)
and get_varunop term bvl =
  let val (oper,l) = strip_comb term in
  let val lhs = hd l in
    get_var lhs bvl
  end end
and get_varbinop term bvl = 
  let val (oper,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in
    (get_var lhs bvl) @ (get_var rhs bvl) 
  end end
and get_varabs bvl1 term bvl2 = 
  (get_varl bvl1 (bvl1 @ bvl2)) @ (get_var term (bvl1 @ bvl2))


fun all_varl term = erase_double (get_var term [])
fun list_all_varl terml = erase_double (get_varl terml [])
(* return a list of triple (variable,number of arguments,category) *)


fun is_in_bval (a,b) = (b = Boundvar)
fun is_in_fval (a,b) = (b = Freevar)
fun is_in_cal (a,b) = (b = Constvar)
fun is_in_fvcal (a,b) = (b = Freevar) orelse (b = Constvar)

fun get_bval term = map fst (filter is_in_bval (all_varl term))
fun get_fval term = map fst (filter is_in_fval (all_varl term))
fun get_cal term = map fst (filter is_in_cal (all_varl term))
fun get_fvcal term = map fst (filter is_in_fvcal (all_varl term))  

fun get_bvl term = map fst (get_bval term)
fun get_fvl term = map fst (get_fval term)
fun get_cl term = map fst (get_cal term)
fun get_fvcl term = map fst (get_fvcal term)
fun all_var term = map fst (map fst (all_varl term))
fun all_vara term = map fst (all_varl term)
fun all_varl terml = list_merge (map all_var terml)

fun concat_thm returnalist thm =
  let val l = (hyp thm) @ [concl thm] in
    list_merge (map returnalist l)
  end 
  
fun get_fvl_thm thm = concat_thm get_fvl thm
fun get_bvl_thm thm = concat_thm get_bvl thm
fun get_cl_thm thm = concat_thm get_cl thm
fun get_fvcl_thm thm = concat_thm get_fvcl thm
fun all_var_thm thm = concat_thm all_var thm
fun all_vara_thm thm = concat_thm all_vara thm

fun concat_goal returnalist goal =
  let val l = fst goal @ [snd goal] in
    list_merge (map returnalist l)
  end
  
fun get_fvl_goal goal = concat_goal get_fvl goal
fun get_bvl_goal goal = concat_goal get_bvl goal
fun get_cl_goal goal = concat_goal get_cl goal
fun get_fvcl_goal goal = concat_goal get_fvcl goal
fun all_var_goal goal = concat_goal all_var goal
fun all_vara_goal goal = concat_goal all_vara goal

end 