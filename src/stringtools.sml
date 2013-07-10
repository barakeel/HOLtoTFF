structure stringtools :> stringtools =
struct

open HolKernel

fun STRINGTOOLS_ERR function message =
  HOL_ERR{origin_structure = "stringtools",
          origin_function = function,
          message = message}

(* modify string *)
fun space n =
  case n of
    0 => ""
  | n => if n > 0 
         then " " ^ (space (n-1))
         else raise STRINGTOOLS_ERR "space" ""

fun indent n = "\n" ^ (space n)

fun last2str str = substring (str,(size str) - 2, 2);

(* test
last2str "hello";
*)


(* name *)
fun name_strn str n = str ^ (Int.toString n) 

fun list_name_str_aux str n = 
  case n of
    0 => []
  | n => if n < 0 then raise STRINGTOOLS_ERR "list_name_str" ""
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

end
