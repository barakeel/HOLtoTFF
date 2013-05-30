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

fun erasedouble list = 
  case list of
    [] => []
  | a :: m => if ismember a m 
              then erasedouble m 
              else a :: erasedouble m

fun map elem couplelist =
  case couplelist of 
  [] => raise LISTTOOLS_ERR "map" ""
  | (a,b) :: m =>  if a = elem then b else map elem m


fun fstcomponent couplel= fst (split couplel)


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


