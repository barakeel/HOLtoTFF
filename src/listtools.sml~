structure listtools :> listtools =
struct

open HolKernel

fun LISTTOOLS_ERR function message =
  HOL_ERR{origin_structure = "listtools",
          origin_function = function,
          message = message}


fun ismember elem list =
  case list of
    [] => false
  | a :: m => if elem = a 
              then true 
              else ismember elem m     

fun isempty list =
  case list of
    [] => true
  | _ => false

fun erasedouble list = 
  case list of
    [] => []
  | a :: m => if ismember a m 
              then erasedouble m 
              else a :: erasedouble m

(* dictionnary *)
fun fstcomponent couplel = 
  case couplel of
    [] => []
  | (a,_) :: m => a :: fstcomponent m

fun erase3rdcomponent triplel =
  case triplel of
    [] => []
  | (a,b,_) :: m => (a,b) :: erase3rdcomponent m

fun erase2ndcomponent triplel =
  case triplel of
    [] => []  
  | (a,_,c) :: m => (a,c) :: erase2ndcomponent m

fun addentry entry dict = 
  if ismember (fst entry) (fstcomponent dict)
  then dict
  else entry :: dict

fun lookup elem couplelist =
  case couplelist of 
  [] => raise LISTTOOLS_ERR "lookup" ""
  | (a,b) :: m =>  if a = elem then b else lookup elem m


(* condition *)
fun switch condresultl defaultresult = 
    case condresultl of
      [] => defaultresult  
    | [(cond,result)] => if cond  
                         then result 
                         else defaultresult
    | (cond,result) :: m => if cond
                            then result
                            else switch m defaultresult                

fun switcherr condresultl error = 
    case condresultl of
      [] => raise LISTTOOLS_ERR "switcherr" "emptylist" 
    | [(cond,result)] => if cond  
                         then result 
                         else (raise error)
    | (cond,result) :: m => if cond
                            then result
                            else switcherr m error

fun switcharg arg condresultl defaultresult = 
    case condresultl of
      [] => defaultresult  
    | [(cond,result)] => if cond arg
                         then result 
                         else defaultresult
    | (cond,result) :: m => if cond arg
                            then result
                            else switcharg arg m defaultresult             
 
fun switchargerr arg condresultl error = 
    case condresultl of
      [] => raise LISTTOOLS_ERR "switchargerr" "emptylist" 
    | [(cond,result)] => if cond arg
                         then result 
                         else (raise error)
    | (cond,result) :: m => if cond arg
                            then result
                            else switchargerr arg m error         

end


