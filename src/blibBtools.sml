structure blibBtools :> blibBtools =
struct

open HolKernel boolLib

fun BTOOLS_ERR function message =
  HOL_ERR {origin_structure = "blibBtools",
	         origin_function = function,
           message = message}

(* FUNCTION *)
fun repeat_n_fun n f x = 
  case n of
    0 => x
  | _ => if n < 0 
         then raise BTOOLS_ERR "repeat_n_fun" "negative number"  
         else f (repeat_n_fun (n - 1) f x)
    
fun inv f a b = f b a

(* ERROR HANDLING *)
fun success f x =
  (f x; true) handle _ => false
  
fun wrap s f m function x =
  function x               
  handle  
    HOL_ERR {origin_structure = s1, origin_function = f1, message = m1}
      => raise HOL_ERR {origin_structure = s ^ " - " ^ s1,
                        origin_function = f ^ " - " ^ f1,
                        message = m ^ " - " ^ m1}           
  | UNCHANGED => raise UNCHANGED
  | _ => raise HOL_ERR {origin_structure = s,
                        origin_function = f,
                        message = m}

(********** STRINGTOOOLS ***********)

(* modify string *)
fun space n =
  case n of
    0 => ""
  | n => if n > 0 
         then " " ^ (space (n-1))
         else raise BTOOLS_ERR "space" ""

fun indent n = "\n" ^ (space n)

fun last2char str = 
  if size str < 2
  then ""
  else substring (str,(size str) - 2, 2);

fun erase_last4char str = 
  if size str < 4 
  then ""
  else substring (str,0,(String.size str)-4)

fun change_to_predty str = (erase_last4char str) ^ "$o"
(* test
last2char "hello";
*)

(* name *)
fun name_strn str n = str ^ (Int.toString n) 

fun list_name_str_aux str n = 
  case n of
    0 => []
  | n => if n < 0 then raise BTOOLS_ERR "list_name_str" ""
         else str ^ (Int.toString n) :: list_name_str_aux str (n - 1)

fun list_name_str str n = rev (list_name_str_aux str n)
(* end name *) 
 
(* test *)
(* warning: include the empty string *)
fun is_alphanumor_charl charl= 
  case charl of
    [] => true    
  | a :: m => (Char.isAlphaNum a orelse (Char.toString a) = "_") 
              andalso is_alphanumor_charl m  

fun is_alphanumor_ str = is_alphanumor_charl (explode str)

(* name supported by the tptp for a free variable or a type *)              
fun is_lowerword str =
  case String.explode str of
    [] => false
  | [a] => Char.isLower a  
  | a :: m => (Char.isLower a) andalso (is_alphanumor_charl m)

(* name supported by the tptp for a bound variable *)
fun is_upperword str =
  case String.explode str of
    [] => false
  | [a] => Char.isUpper a  
  | a :: m => (Char.isUpper a) andalso (is_alphanumor_charl m)
  
  
(********* LISTTOOLS **********) 
fun make_list_n n a =
  case n of 
    0 => []
  | _ => if n < 0 then raise BTOOLS_ERR "make_n_emptyl" "negative number"
         else
           a :: make_list_n (n -1) a

(* NUMBER *)
fun suml nl =
  case nl of
    [] => 0
  | n :: m => n + suml m
  
fun multl al bl =
  if not (length al = length bl) 
  then raise BTOOLS_ERR "multl" "different length"
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

fun strict_subset s1 s2 = subset s1 s2 andalso not (s1 = s2)

fun is_maxset s sl = not (exists (strict_subset s) sl)

fun list_subset ll1 ll2 =
  if not (length ll1 = length ll2) 
  then 
    raise BTOOLS_ERR "list_subset" "different length" 
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
  [] => (elem; raise BTOOLS_ERR "lookup" "")
  | (a,b) :: m =>  if a = elem then b else lookup elem m



(* condition *)
fun make_list_n n a =
  case n of 
    0 => []
  | _ => if n < 0 then raise BTOOLS_ERR "make_n_emptyl" "negative number"
         else
           a :: make_list_n (n -1) a

(* NUMBER *)
fun suml nl =
  case nl of
    [] => 0
  | n :: m => n + suml m
  
fun multl al bl =
  if not (length al = length bl) 
  then raise BTOOLS_ERR "multl" "different length"
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

fun strict_subset s1 s2 = subset s1 s2 andalso not (s1 = s2)

fun is_maxset s sl = not (exists (strict_subset s) sl)

fun list_subset ll1 ll2 =
  if not (length ll1 = length ll2) 
  then 
    raise BTOOLS_ERR "list_subset" "different length" 
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
  [] => (elem; raise BTOOLS_ERR "lookup" "")
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
      [] => raise BTOOLS_ERR "switcherr" "emptylist" 
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
      [] => raise BTOOLS_ERR "switchargerr" "emptylist" 
    | [(cond,result)] => if cond arg
                         then result 
                         else (raise error)
    | (cond,result) :: m => if cond arg
                            then result
                            else switchargerr arg m error         
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
      [] => raise BTOOLS_ERR "switcherr" "emptylist" 
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
      [] => raise BTOOLS_ERR "switchargerr" "emptylist" 
    | [(cond,result)] => if cond arg
                         then result 
                         else (raise error)
    | (cond,result) :: m => if cond arg
                            then result
                            else switchargerr arg m error         
  
end
  