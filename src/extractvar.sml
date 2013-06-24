structure extractvar :> extractvar =
struct

open HolKernel listtools mydatatype Term

fun EXTRACTVAR_ERR function message =
  HOL_ERR{origin_structure = "extractvar",
          origin_function = function,
          message = message}

(* warning: should have the same structure as printterm in printtff.sml *)
(* extract a list of triple (variable,nombre d'arguments,category) *)
(* detect second order clash with bound variables *)

fun extractvar2 term bvl =
  case termstructure term of
    Numeral => [((term,0),Numeralvar)]
  | Var => if is_member term bvl
           then [((term,0),Boundvar)] 
           else [((term,0),Freevar)]
  | Const => [((term,0),Constvar)]
  | Comb => (
            case connective term of
              Conj => extractvar2binop term bvl
            | Disj => extractvar2binop term bvl
            | Neg => extractvar2unop term bvl
            | Imp_only => extractvar2binop term bvl
            | Forall => let val (qbvl,t) = strip_forall term in
                          extractvar2quantifier qbvl t bvl
                        end       
            | Exists => let val (qbvl,t) = strip_exists term in
                          extractvar2quantifier qbvl t bvl 
                        end
            | App => let val (operator,argl) = strip_comb term in
                     let 
                       val n = length argl 
                       val l = extractvar2l argl bvl 
                     in
                       case termstructure operator of
                         Numeral => raise EXTRACTVAR_ERR "extractvar2" "operator is numeral"
                       | Var =>  if is_member operator bvl
                                 then ((operator,n),Boundvar) :: l
                                 else ((operator,n),Freevar) :: l
                       | Const => ((operator,n),Constvar) :: l
                       | Comb => raise EXTRACTVAR_ERR "extractvar2" "operator is a combination"
                       | Abs => raise EXTRACTVAR_ERR "extractvar2" "abstraction"
                     end end
             )
  | Abs => raise EXTRACTVAR_ERR "extractvar2" "abstraction"
and extractvar2l terml bvl = 
  case terml of
    [] => raise EXTRACTVAR_ERR "extractvar2l" "emptylist"
  | [t] => extractvar2 t bvl
  | t :: m => (extractvar2 t bvl) @ (extractvar2l m bvl)
and extractvar2unop term bvl =
  let val (operator,l) = strip_comb term in
  let val lhs = hd l in
    extractvar2 lhs bvl
  end end
and extractvar2binop term bvl = 
  let val (operator,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in
    (extractvar2 lhs bvl) @ (extractvar2 rhs bvl) 
  end end
and extractvar2quantifier qbvl term bvl = 
  (extractvar2l qbvl (qbvl @ bvl)) @ (extractvar2 term (qbvl @ bvl))

fun erase_number l =
  case l of 
    [] => []
  | (_,Numeralvar) :: m => erase_number m 
  | a :: m =>  a :: erase_number m


fun extractvar term = erase_number (erase_double (extractvar2 term [])) 
fun extractvarl terml = erase_number (erase_double (extractvar2l terml []))
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

fun get_fvcl_thm thm = 
  let
    val hypl = hyp thm
    val goal = concl thm
  in
   let val varacat = extractvarl (hypl @ [goal]) in
   let val fvcal = get_fvcal varacat in
     fstcomponent fvcal
   end end
  end


end 