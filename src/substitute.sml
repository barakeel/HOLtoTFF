structure substitute :> substitute =
struct

open HolKernel 


(* a definition is a theorem of the form 
( [] |- term = definition_of_term ) *)  

val thm = ASSUME ``?!a. a = b``;


(* beta reduction *)
(* *)
(*  should do monomorphism first *)
(* two different set definitions and axioms *)

SUBS [EXISTS_UNIQUE_DEF] thm;



fun replaceby_def_in def thm =
  
  

end