structure extractterm :> extractterm =
struct

open HolKernel listtools mydatatype

fun EXTRACTTERM_ERR function message =
  HOL_ERR{origin_structure = "extractterm",
          origin_function = function,
          message = message}

(*warning: should have the same structure as printterm in printtff.sml*)
fun getfvc term bvl = 
  case termstructure term of
    Numeral => [] 
  | Var => if ismember term bvl
           then [] (*boundvar*)
           else [term] (*freevar*)
  | Const => (
             case leafconst term of
               True => []
             | False => []
             | Newleafconst => [term]
             )
  | Comb => (
            case connective term of
              Conj => getfvcbinop term bvl
            | Disj => getfvcbinop term bvl
            | Neg => getfvcunop term bvl
            | Imp_only => getfvcbinop term bvl
            | Forall => let val (qbvl,t) = strip_forall term in
                          getfvc t (qbvl @ bvl)
                        end       
            | Exists => let val (qbvl,t) = strip_exists term in
                          getfvc t (qbvl @ bvl) 
                        end
            | App => let val (operator,argl) = strip_comb term in
                     let val l = getfvcl2 argl bvl in
                       case termstructure operator of
                         Numeral => raise EXTRACTTERM_ERR "printterm" "numeralisnotanoperator"
                       | Var => operator :: l
                       | Const => (
                                  case nodeconst term of
                                    Newnodeconst => operator :: l    
                                  | _ => l (*we don't need a name and a definition for defined tff constant*)
                                  )
                       | Comb => raise EXTRACTTERM_ERR "printterm" "secondorder"
                       | Abs => raise EXTRACTTERM_ERR "printterm" "abstraction"
                     end end
             )
  | Abs => raise EXTRACTTERM_ERR "printterm" "abstraction"
and getfvcl2 list bvl = 
  case list of
    [] => raise EXTRACTTERM_ERR "printterml" "emptylist"
  | [t] => getfvc t bvl
  | t :: m => (getfvc t bvl) @ (getfvcl2 m bvl)
and getfvcunop term bvl =
  let val (operator,l) = strip_comb term in
  let val lhs = hd l in
    getfvc lhs bvl
  end end
and getfvcbinop term bvl = 
  let val (operator,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in
    (getfvc lhs bvl) @ (getfvc rhs bvl) 
  end end

fun getfvcl termlist = erasedouble (getfvcl2 termlist [])

end
