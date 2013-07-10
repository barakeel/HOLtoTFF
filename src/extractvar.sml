structure extractvar :> extractvar =
struct

(*
load "listtools"; open listtools;
load "mydatatype"; open mydatatype;
*)

open HolKernel 
     listtools mydatatype


fun EXTRACTVAR_ERR function message =
  HOL_ERR{origin_structure = "extract_var",
          origin_function = function,
          message = message}

(* warning: should have the same structure as print_term in printtff.sml *)
(* extract a list of triple (variable,nombre d'arguments,category) *)
(* detect second order clash with bound variables *)
(* used to get arity *)

fun extract_var2 term bvl =
  case termstructure term of
    Numeral => [((term,0),Numeralvar)]
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
      Conj => extract_var2binop term bvl
    | Disj => extract_var2binop term bvl
    | Neg => extract_var2unop term bvl
    | Imp_only => extract_var2binop term bvl
    | Forall => let val (qbvl,t) = strip_forall term in
                  extract_var2abs qbvl t bvl
                end       
    | Exists => let val (qbvl,t) = strip_exists term in
                  extract_var2abs qbvl t bvl 
                end
    | App => let val (operator,argl) = strip_comb term in
             let 
               val n = length argl 
               val l = extract_var2l argl bvl 
             in
             case termstructure operator of
               Numeral => raise EXTRACTVAR_ERR "extract_var2" "operator is num"
             | Var =>  if is_member operator bvl
                       then ((operator,n),Boundvar) :: l
                       else ((operator,n),Freevar) :: l
             | Const => ((operator,n),Constvar) :: l
             | Comb => raise EXTRACTVAR_ERR "extract_var2" "operator is comb"
             | Abs => let val (absbvl,t) = strip_abs operator in
                        extract_var2abs absbvl t bvl @ l
                      end  
             end end
    )         
  | Abs => let val (absbvl,t) = strip_abs term in
             extract_var2abs absbvl t bvl 
           end  
and extract_var2l terml bvl = 
  case terml of
    [] => [] 
  | t :: m => (extract_var2 t bvl) @ (extract_var2l m bvl)
and extract_var2unop term bvl =
  let val (operator,l) = strip_comb term in
  let val lhs = hd l in
    extract_var2 lhs bvl
  end end
and extract_var2binop term bvl = 
  let val (operator,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in
    (extract_var2 lhs bvl) @ (extract_var2 rhs bvl) 
  end end
and extract_var2abs bvl1 term bvl2 = 
  (extract_var2l bvl1 (bvl1 @ bvl2)) @ (extract_var2 term (bvl1 @ bvl2))



fun erase_number l =
  case l of 
    [] => []
  | (_,Numeralvar) :: m => erase_number m 
  | a :: m =>  a :: erase_number m

fun erase_bv l =
  case l of 
    [] => []
  | (_,Boundvar) :: m => erase_bv m 
  | a :: m =>  a :: erase_bv m
  
fun extract_var term = erase_number (erase_double (extract_var2 term [])) 
fun extract_varl terml = erase_number (erase_double (extract_var2l terml []))
(* return a list of triple (variable,number of arguments,category) *)

(* lowest arity *)
(* can be applied to any category but mostly for constant and free variables *)
fun get_lowestarity (term,arity) termal =
  case termal of
    [] => arity
  | (t,a) :: m => if term = t 
                  then 
                    if a < arity 
                    then get_lowestarity (term,a) m
                    else get_lowestarity (term,arity) m 
                  else get_lowestarity (term,arity) m     
;
(* quadratic *)
(* merge free and bound variables *)
fun nullify_boundarity varacat =
  case varacat of
    [] => []
  | ((var,arity),Boundvar) :: m => ((var,0),Boundvar) :: nullify_boundarity m
  | a :: m => a :: nullify_boundarity m
  
fun collapse_lowestarity2 varalfix varal =
  case varal of
    [] => []
  | (var,arity) :: m => 
    let val lowestarity = get_lowestarity (var,arity) varalfix in
      (var,lowestarity) :: collapse_lowestarity2 varalfix m
    end
  
fun collapse_lowestarity varal = 
  erase_double (collapse_lowestarity2 varal varal)
  
(* end lowestarity *)

fun get_bval l =   
  case l of 
    [] => []
  | (bva,Boundvar) :: m => bva :: get_bval m
  | a :: m => get_bval m

fun get_fval l =   
  case l of 
    [] => []
  | (fva,Freevar) :: m => fva :: get_fval m
  | a :: m => get_fval m

fun get_cal l =   
  case l of 
    [] => []
  | (ca,Constvar) :: m => ca :: get_cal m
  | a :: m => get_cal m

fun get_fvcal l = get_fval l @ get_cal l

(* for thm easy extraction *)
fun get_fvcl_thm thm = 
  let
    val hypl = hyp thm
    val goal = concl thm
  in
   let val varacat = extract_varl (hypl @ [goal]) in
   let val fvcal = get_fvcal varacat in
     map fst fvcal
   end end
  end

fun get_cl_thm thm = 
  let
    val hypl = hyp thm
    val goal = concl thm
  in
   let val varacat = extract_varl (hypl @ [goal]) in
   let val cal = get_cal varacat in
     map fst cal
   end end
  end

end 