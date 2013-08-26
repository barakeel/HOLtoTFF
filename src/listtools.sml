structure listtools :> listtools =
struct

open HolKernel Abbrev boolLib basictools

fun LISTTOOLS_ERR function message =
  HOL_ERR{origin_structure = "listtools",
          origin_function = function,
          message = message}


fun make_list_n n a =
  case n of 
    0 => []
  | _ => if n < 0 then raise LISTTOOLS_ERR "make_n_emptyl" "negative number"
         else
           a :: make_list_n (n -1) a

(* NUMBER *)
fun suml nl =
  case nl of
    [] => 0
  | n :: m => n + suml m
  
fun multl al bl =
  if not (length al = length bl) 
  then raise LISTTOOLS_ERR "multl" "different length"
  else
    case al of
      [] => []
    | _  => (hd al) * (hd bl) :: multl (tl al) (tl bl) 

(* SET *)
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
  if is_member elem list then list else elem :: list
 
fun inter l1 l2 = filter (inv is_member l2) l1 

fun subset l1 l2 = all (inv is_member l2) l1

fun list_subset ll1 ll2 =
  if not (length ll1 = length ll2) 
  then 
    raise LISTTOOLS_ERR "list_subset" "different length" 
  else 
    case ll1 of
      [] => true
    | _  => subset (hd ll1) (hd ll2) andalso
            list_subset (tl ll1) (tl ll2)
    
fun list_merge ll = erase_double (List.concat ll)

fun quicksort << xs = let
  fun qs [] = []
    | qs [x] = [x]
    | qs (p::xs) = let
        val lessThanP = (fn x => << (x, p))
        in
          qs (filter lessThanP xs) @ p :: (qs (filter (not o lessThanP) xs))
        end
  in
    qs xs
  end
 
fun repeatchange change l changing = 
  case l of
    [] => changing
  | a :: m => repeatchange change m (change a changing)


(* dictionnary *)
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


