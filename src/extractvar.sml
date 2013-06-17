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
    Numeral => [(term,0,Number)]
  | Var => if ismember term bvl
           then [(term,0,Bound)] 
           else [(term,0,Free)]
  | Const => (
             case leafconst term of
               True => [(term,0,Tffconst)] 
             | False => [(term,0,Tffconst)] 
             | Newleafconst => [(term,0,Undefconst)] 
             )
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
                       | Var =>  if ismember operator bvl
                                 then (operator,n,Bound) :: l
                                 else (operator,n,Free) :: l
                       | Const => (
                                  case nodeconst term of
                                    Newnodeconst => (operator,n,Undefconst) :: l
                                  | _ => (operator,n,Tffconst) :: l
                                  )
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

fun erasenumber l =
  case l of 
    [] => []
  | (_,_,Number) :: m => erasenumber m 
  | a :: m =>  a :: erasenumber m


fun extractvar term = erasenumber (erasedouble (extractvar2 term [])) 
fun extractvarl terml = erasenumber (erasedouble (extractvar2l terml []))
(* return a list of triple (variable,number of arguments,category) *)

fun erasebv l =
  case l of 
    [] => []
  | (_,_,Bound) :: m => erasebv m 
  | a :: m =>  a :: erasebv m


fun getbvnargl l =   
  case l of 
    [] => []
  | (bv,narg,Bound) :: m => (bv,narg) :: getbvnargl m
  | a :: m => getbvnargl m

fun getfvcnargl l =   
  case l of 
    [] => []
  | (fv,narg,Free) :: m => (fv,narg) :: getfvcnargl m
  | (c,narg,Undefconst) :: m => (c,narg) :: getfvcnargl m
  | a :: m => getfvcnargl m


end
