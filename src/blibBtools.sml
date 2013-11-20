structure blibBtools :> blibBtools =
struct

open HolKernel boolLib

fun BTOOLS_ERR function message =
  HOL_ERR {origin_structure = "blibBtools",
	         origin_function = function,
           message = message}

(*********** FUNCTION **********)
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
fun space n =
  case n of
    0 => ""
  | n => if n > 0 
         then " " ^ (space (n-1))
         else raise BTOOLS_ERR "space" ""

fun indent n = "\n" ^ (space n)

fun first_n_char n str = String.substring (str,0,n)
fun rm_first_n_char n str = String.substring (str,n,String.size str - n)

fun last_n_char n str = String.substring (str,String.size str - n,n)
fun rm_last_n_char n str = String.substring (str,0,String.size str - n)



fun char_place_aux ch str n =
  if first_n_char 1 str = ch then n
  else char_place_aux ch (rm_first_n_char 1 str) (n + 1)
fun char_place ch str = char_place_aux ch str 0

fun char_in ch str = success (char_place ch) str 


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

fun string_to_int_aux l =
  case l of
    [] => 0
  | c :: m => case Char.toString c of 
                "0" => 0 + 10 * (string_to_int_aux m)
              | "1" => 1 + 10 * (string_to_int_aux m)
              | "2" => 2 + 10 * (string_to_int_aux m)
              | "3" => 3 + 10 * (string_to_int_aux m)
              | "4" => 4 + 10 * (string_to_int_aux m)
              | "5" => 5 + 10 * (string_to_int_aux m)
              | "6" => 6 + 10 * (string_to_int_aux m)
              | "7" => 7 + 10 * (string_to_int_aux m)
              | "8" => 8 + 10 * (string_to_int_aux m)
              | "9" => 9 + 10 * (string_to_int_aux m)
              | _   => raise BTOOLS_ERR "string_to_int" 
                         ((String.implode l) ^ " not a number")
                         
fun string_to_int str = string_to_int_aux (rev (String.explode str))

(********* LISTTOOLS **********) 
fun mk_list n a =
  if n < 0 then raise BTOOLS_ERR "mk_list" "negative number"
  else
    case n of 
      0 => []
    | _ => a :: mk_list (n -1) a

fun mk_reflist n a =
  if n < 0 then raise BTOOLS_ERR "mk_reflist" "negative number"
  else
    case n of 
      0 => []
    | _ => (ref a) :: mk_reflist (n -1) a
  

fun nth n l =
  if n < 0 then raise BTOOLS_ERR "nth" "list too short"
  else
    case n of 
      0 => hd l
    | _ => nth (n-1) (tl l)
   
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

fun remove elem list = 
  case list of
    [] => []
  | a :: m => if a = elem then remove elem m else a :: remove elem m
 
fun inter l1 l2 = filter (inv is_member l2) l1 

fun substract l1 l2 = filter (not o (inv is_member) l2) l1

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
    
fun merge ll = erase_double (List.concat ll)

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
 
fun repeat_change change l changing = 
  case l of
    [] => changing
  | a :: m => repeat_change change m (change a changing)


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
fun mk_list n a =
  case n of 
    0 => []
  | _ => if n < 0 then raise BTOOLS_ERR "make_n_emptyl" "negative number"
         else
           a :: mk_list (n -1) a

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
 
(* FILE MANAGEMENT *)
fun readl filepath = 
  let
    val file = TextIO.openIn filepath
    fun loop file =
      case TextIO.inputLine file of
        SOME line => line :: loop file
      | NONE      => []
  in
    loop file before TextIO.closeIn file
  end 
  
fun outputl file linel =
  case linel of
    [] => ()
  | line :: m => (TextIO.output (file,line ^ "\n"); outputl file m) 
  
fun appendl filepath linel =
  let val file = TextIO.openAppend filepath in 
    (outputl file linel;
     TextIO.closeOut file)  
  end  
 
fun outputll file linel1 linel2 =
  if not (length linel1 = length linel2)
  then
    raise BTOOLS_ERR "outputll" "lists of different length"
  else 
    case (linel1,linel2) of
      ([],_) => ()
    | (_,[]) => ()  
    | (l1 :: m1,l2 :: m2) => (TextIO.output (file,l1 ^ " : " ^ l2 ^ "\n"); 
                                    outputll file m1 m2)  

fun appendll filepath linel1 linel2 =
  let val file = TextIO.openAppend filepath in 
    (outputll file linel1 linel2;
     TextIO.closeOut file)  
  end     

 
end
  