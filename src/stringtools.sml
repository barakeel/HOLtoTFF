structure stringtools :> stringtools =
struct

open HolKernel

fun STRINGTOOLS_ERR function message =
  HOL_ERR{origin_structure = "stringtools",
          origin_function = function,
          message = message}

fun erasechar str =
  if (String.size str) > 0
  then String.extract (str,1,NONE)
  else raise STRINGTOOLS_ERR "erasechar" ""

fun space n =
  case n of
    0 => ""
  | n => if n > 0 
         then " " ^ (space (n-1))
         else raise STRINGTOOLS_ERR "space" ""

fun indent n = "\n" ^ (space n)

(*warning: include the empty string*)
fun isalphanumor_charl charl= 
  case charl of
    [] => true    
  | a :: m => (Char.isAlphaNum a orelse (Char.toString a) = "_") 
              andalso isalphanumor_charl m  

fun isalphanumor_ str = isalphanumor_charl (explode str)

(*name supported by the tptp for a free variable or a type*)              
fun islowerword str =
  case String.explode str of
    [] => false
  | [a] => Char.isLower a  
  | a :: m => (Char.isLower a) andalso (isalphanumor_charl m)

(*name supported by the tptp for a bound variable*)
fun isupperword str =
  case String.explode str of
    [] => false
  | [a] => Char.isUpper a  
  | a :: m => (Char.isUpper a) andalso (isalphanumor_charl m)

end
