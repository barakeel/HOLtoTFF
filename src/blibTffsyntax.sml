structure blibTffsyntax :> blibTffsyntax =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype
     blibSyntax
     
fun TFFSYNTAX_ERR function message =
  HOL_ERR {origin_structure = "blibTffsyntax",
           origin_function = function,
           message = message}


(* WRITER *)
(* hack NLIA *)
fun contain_numfvc term = not (null (filter has_numty (all_vars term)))
fun contain_intfvc term = not (null (filter has_intty (all_vars term)))

fun linearn term =
  case structcomb term of
    Multn => 
      let val (t1,t2) = numSyntax.dest_mult term in
        not (contain_numfvc t1 andalso contain_numfvc t2)
      end
  | _    => raise TFFSYNTAX_ERR "linearn" "not a numeral product"

fun lineari term =
  case structcomb term of
    Multi => 
      let val (t1,t2) = intSyntax.dest_mult term in
        not (contain_numfvc t1 andalso contain_numfvc t2)
      end
  | _    => raise TFFSYNTAX_ERR "lineari" "not a integer product"
  
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

(* name for variables *)
fun name_tff str var =
  let val name = name_of var in 
    if is_alphanumor_ name then str ^ name else str
  end
  
(* READER *)  
(* test for positive integers *)
fun is_numword str = success string_to_int str
(* test for defined names *)
fun is_opword str = false (* wip is_member str (map fst ropdict) *)   

end