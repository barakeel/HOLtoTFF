structure blibExtractvar :> blibExtractvar =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype

fun EXTRACTVAR_ERR function message =
  HOL_ERR{origin_structure = "blibExtractvar",
          origin_function = function,
          message = message}


fun get_varinfol2 term bvl =
  case termstructure term of
    Numeral => [((term,0),Numeralvar)]
  | Integer => [((term,0),Integervar)]
  | Var => if is_member term bvl
           then [((term,0),Boundvar)] 
           else [((term,0),Freevar)]
  | Const => (
             case leafconst term of
               True => []
             | False => []
             | Newleafconst => [((term,0),Constvar)]
             )
  | Comb => 
    (
    case connector term of
      Conj => get_varinfol2binop term bvl
    | Disj => get_varinfol2binop term bvl
    | Neg => get_varinfol2unop term bvl
    | Imp_only => get_varinfol2binop term bvl
    | Forall => let val (qbvl,t) = strip_forall term in
                  get_varinfol2abs qbvl t bvl
                end       
    | Exists => let val (qbvl,t) = strip_exists term in
                  get_varinfol2abs qbvl t bvl 
                end
    | App => let val (operator,argl) = strip_comb term in
             let 
               val n = length argl 
               val l = get_varinfol2l argl bvl 
             in
             case termstructure operator of
               Numeral => raise EXTRACTVAR_ERR "get_varinfol2" "operator is num"
             | Integer => raise EXTRACTVAR_ERR "get_varinfol2" "operator is int"
             | Var =>  if is_member operator bvl
                       then ((operator,n),Boundvar) :: l
                       else ((operator,n),Freevar) :: l
             | Const => ((operator,n),Constvar) :: l
             | Comb => raise EXTRACTVAR_ERR "get_varinfol2" "operator is comb"
             | Abs => let val (absbvl,t) = strip_abs operator in
                        get_varinfol2abs absbvl t bvl @ l
                      end  
             end end
    )         
  | Abs => let val (absbvl,t) = strip_abs term in
             get_varinfol2abs absbvl t bvl 
           end  
and get_varinfol2l terml bvl = 
  case terml of
    [] => [] 
  | t :: m => (get_varinfol2 t bvl) @ (get_varinfol2l m bvl)
and get_varinfol2unop term bvl =
  let val (operator,l) = strip_comb term in
  let val lhs = hd l in
    get_varinfol2 lhs bvl
  end end
and get_varinfol2binop term bvl = 
  let val (operator,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in
    (get_varinfol2 lhs bvl) @ (get_varinfol2 rhs bvl) 
  end end
and get_varinfol2abs bvl1 term bvl2 = 
  (get_varinfol2l bvl1 (bvl1 @ bvl2)) @ (get_varinfol2 term (bvl1 @ bvl2))


fun erase_number l =
  case l of 
    [] => []
  | (_,Numeralvar) :: m => erase_number m 
  | (_,Integervar) :: m => erase_number m 
  | a :: m =>  a :: erase_number m

fun get_varinfol term = erase_number (erase_double (get_varinfol2 term [])) 
fun list_get_varinfol terml = erase_number (erase_double (get_varinfol2l terml []))
(* return a list of triple (variable,number of arguments,category) *)




fun is_in_bval (a,b) = (b = Boundvar)
fun is_in_fval (a,b) = (b = Freevar)
fun is_in_cal (a,b) = (b = Constvar)
fun is_in_fvcal (a,b) = (b = Freevar) orelse (b = Constvar)

fun get_bval term = map fst (filter is_in_bval (get_varinfol term))
fun get_fval term = map fst (filter is_in_fval (get_varinfol term))
fun get_cal term = map fst (filter is_in_cal (get_varinfol term))
fun get_fvcal term = map fst (filter is_in_fvcal (get_varinfol term))  

fun get_bvl term = map fst (get_bval term)
fun get_fvl term = map fst (get_fval term)
fun get_cl term = map fst (get_cal term)
fun get_fvcl term = map fst (get_fvcal term)
fun all_var term = map fst (map fst (get_varinfol term))
fun all_vara term = map fst (get_varinfol term)
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