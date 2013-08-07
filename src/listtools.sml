structure listtools :> listtools =
struct

open HolKernel Abbrev boolLib

fun LISTTOOLS_ERR function message =
  HOL_ERR{origin_structure = "listtools",
          origin_function = function,
          message = message}


fun is_member_eq equal elem list  = exists (equal elem) list

fun erase_double_eq equal list  =
  case list of
   [] => []
 | a :: m => if is_member_eq equal a m 
             then erase_double_eq equal m 
             else a :: erase_double_eq equal m

local fun equal x y = (x = y) in
  fun is_member elem list = is_member_eq equal elem list 
  fun erase_double list = erase_double_eq equal list 
end

fun add_once elem list =
  if is_member elem list 
  then list
  else elem :: list
   
(* dictionnary *)
  (* repeat tools *)
fun repeatchange change l changing = 
  case l of
    [] => changing
  | a :: m => repeatchange change m (change a changing)

  (* doesn't overwrite only the first add entry can do something *)
fun add_entry entry dict = 
  if is_member (fst entry) (map fst dict)
  then dict
  else entry :: dict

fun lookup elem couplelist =
  case couplelist of 
  [] => (elem; raise LISTTOOLS_ERR "lookup" "")
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


