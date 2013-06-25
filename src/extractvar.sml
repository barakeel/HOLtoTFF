structure extractvar :> extractvar =
struct

open HolKernel listtools mydatatype Term

fun EXTRACTVAR_ERR function message =
  HOL_ERR{origin_structure = "extract_var",
          origin_function = function,
          message = message}

(* warning: should have the same structure as printterm in printtff.sml *)
(* extract a list of triple (variable,nombre d'arguments,category) *)
(* detect second order clash with bound variables *)

fun extract_var2 term bvl =
  case termstructure term of
    Numeral => [((term,0),Numeralvar)]
  | Var => if is_member term bvl
           then [((term,0),Boundvar)] 
           else [((term,0),Freevar)]
  | Const => [((term,0),Constvar)]
  | Comb => (
            case connective term of
              Conj => extract_var2binop term bvl
            | Disj => extract_var2binop term bvl
            | Neg => extract_var2unop term bvl
            | Imp_only => extract_var2binop term bvl
            | Forall => let val (qbvl,t) = strip_forall term in
                          extract_var2quantifier qbvl t bvl
                        end       
            | Exists => let val (qbvl,t) = strip_exists term in
                          extract_var2quantifier qbvl t bvl 
                        end
            | App => let val (operator,argl) = strip_comb term in
                     let 
                       val n = length argl 
                       val l = extract_var2l argl bvl 
                     in
                       case termstructure operator of
                         Numeral => raise EXTRACTVAR_ERR "extract_var2" "operator is numeral"
                       | Var =>  if is_member operator bvl
                                 then ((operator,n),Boundvar) :: l
                                 else ((operator,n),Freevar) :: l
                       | Const => ((operator,n),Constvar) :: l
                       | Comb => raise EXTRACTVAR_ERR "extract_var2" "operator is a combination"
                       | Abs => raise EXTRACTVAR_ERR "extract_var2" "abstraction"
                     end end
             )
  | Abs => raise EXTRACTVAR_ERR "extract_var2" "abstraction"
and extract_var2l terml bvl = 
  case terml of
    [] => raise EXTRACTVAR_ERR "extract_var2l" "emptylist"
  | [t] => extract_var2 t bvl
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
and extract_var2quantifier qbvl term bvl = 
  (extract_var2l qbvl (qbvl @ bvl)) @ (extract_var2 term (qbvl @ bvl))

fun erase_number l =
  case l of 
    [] => []
  | (_,Numeralvar) :: m => erase_number m 
  | a :: m =>  a :: erase_number m


fun extract_var term = erase_number (erase_double (extract_var2 term [])) 
fun extract_varl terml = erase_number (erase_double (extract_var2l terml []))
(* return a list of triple (variable,number of arguments,category) *)

fun erase_bv l =
  case l of 
    [] => []
  | (_,Boundvar) :: m => erase_bv m 
  | a :: m =>  a :: erase_bv m

fun get_bval l =   
  case l of 
    [] => []
  | (bva,Boundvar) :: m => bva :: get_bval m
  | a :: m => get_bval m

fun get_fvcal l =   
  case l of 
    [] => []
  | (fva,Freevar) :: m => fva :: get_fvcal m
  | (ca,Constvar) :: m => ca :: get_fvcal m
  | a :: m => get_fvcal m

fun get_cal l =   
  case l of 
    [] => []
  | (ca,Constvar) :: m => ca :: get_cal m
  | a :: m => get_cal m

fun get_fvcl_thm thm = 
  let
    val hypl = hyp thm
    val goal = concl thm
  in
   let val varacat = extract_varl (hypl @ [goal]) in
   let val fvcal = get_fvcal varacat in
     fstcomponent fvcal
   end end
  end

fun get_cl_thm thm = 
  let
    val hypl = hyp thm
    val goal = concl thm
  in
   let val varacat = extract_varl (hypl @ [goal]) in
   let val cal = get_cal varacat in
     fstcomponent cal
   end end
  end

end 