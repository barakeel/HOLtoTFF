structure blibTffsyntax :> blibTffsyntax =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype
     blibSyntax blibExtracttype
     
fun TFFSYNTAX_ERR function message =
  HOL_ERR {origin_structure = "blibTffsyntax",
           origin_function = function,
           message = message}

(* TEST *)
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

(* name for positive integers *)
fun is_numword str = success string_to_int str
  
(* utilise les numéraux  ou les entiers*)
val dcprintdict = [
   (Plusn,"$sum"),
   (Minusn,"$difference"),
   (Multn,"$product"),
   (Lessn,"$less"),
   (Leqn,"$lesseq"),
   (Greatern,"$greater"),
   (Geqn,"$greatereq"),
   (Plusi,"$sum"),
   (Minusi,"$difference"),
   (Multi,"$product"),
   (Lessi,"$less"),
   (Leqi,"$lesseq"),
   (Greateri,"$greater"),
   (Geqi,"$greatereq"),
   (Negated,"$uminus")
   ]

val rdcdict = [
(* 
  ("$sum",intSyntax.plus_tm),
  ("$difference",intSyntax.minus_tm),
  ("$product",intSyntax.mult_tm),
  ("$less",intSyntax.less_tm),
  ("$lesseq",intSyntax.leq_tm),
  ("$greater",intSyntax.great_tm),
  ("$greatereq",intSyntax.geq_tm),
  ("$uminus",intSyntax.negate_tm) 
*)
  ]  

(* defined names *)
fun is_defword str = is_member str (map fst rdcdict)
 
(* VAR NAME *)
fun name_tff str var =
  let val name = name_of var in 
    if is_alphanumor_ name then str ^ name else str
  end
  

(* DEFINED TFF CONSTANTS *)
val dcl = [(*
           plus_tm,minus_tm,mult_tm,less_tm,leq_tm,great_tm,geq_tm,negate_tm,
           *)
           numSyntax.plus_tm,numSyntax.minus_tm,numSyntax.mult_tm,
           numSyntax.less_tm,numSyntax.greater_tm,
           numSyntax.geq_tm]

fun is_dc var = 
  (is_member var dcl orelse name_of var = "=") handle _ => false

fun is_dca (term,arity) = 
  (is_dc term andalso arity = 2) orelse (name_of term = "=" andalso arity = 2)

fun is_dcaty ((term,arity),str) = is_dca (term,arity)

(* non linear arithmetic hack *)
val dcl2 = substract dcl [(*mult_tm,*)numSyntax.mult_tm]  
fun is_dc2 var = 
  is_member var dcl2 orelse name_of var = "=" handle _ => false

fun is_dca2 (term,arity) = 
  (is_dc2 term andalso arity = 2) orelse (name_of term = "=" andalso arity = 2)

fun is_dcaty2 ((term,arity),str) = is_dca2 (term,arity)
  
(* DEFINED TFF TYPES *) (* all types starting with "$" *)
fun is_dtyname name = (substring (name,0,1) = "$")
fun has_not_dtyname ((ty,arity),name) = (not o is_dtyname) name  
fun erase_dtyname tyadict = filter has_not_dtyname tyadict
    

end