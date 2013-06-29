structure listtools :> listtools =
struct

open HolKernel

fun LISTTOOLS_ERR function message =
  HOL_ERR{origin_structure = "listtools",
          origin_function = function,
          message = message}

fun is_member elem list =
  case list of
    [] => false
  | a :: m => if elem = a 
              then true 
              else is_member elem m     

fun is_empty list =
  case list of
    [] => true
  | _ => false

fun erase_double list = 
  case list of
    [] => []
  | a :: m => if is_member a m 
              then erase_double m 
              else a :: erase_double m

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
  [] => raise LISTTOOLS_ERR "lookup" ""
  | (a,b) :: m =>  if a = elem then b else lookup elem m

fun rename name used =
  let val nameref = ref name in 
  let val nref = ref 0 in
    (
    while is_member (!nameref) used
    do
      (nameref := (!nameref) ^ (Int.toString (!nref));
       nref := (!nref) + 1) 
    ;
    !nameref
    )
  end end

(* all dict are injective dict this way *)
fun addrename (key,name) dict =
  let val newname = rename name (map snd dict) in
    add_entry (key,newname) dict
  end  

fun addrenamel entry dict = repeatchange addrename entry dict

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


