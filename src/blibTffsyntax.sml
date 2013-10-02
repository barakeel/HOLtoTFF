structure blibTffsyntax :> blibTffsyntax =
struct

open HolKernel Abbrev boolLib numSyntax
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
  
  
val rdcdict = [
  ("$sum",plus_tm),
  ("$difference",minus_tm),
  ("$product",mult_tm),
  ("$less",less_tm),
  ("$lesseq",leq_tm),
  ("$greater",greater_tm),
  ("$greatereq",geq_tm)
  ]  

(* defined names *)
fun is_defword str = is_member str (map fst rdcdict)
 
(* VAR NAME *)
fun name_tff str var =
  let val name = name_of var in 
    if is_alphanumor_ name then str ^ name else str
  end
  
  
  
  
  
(* DEFINED TFF CONSTANTS *)
val dcdict = [
   (Plus,"$sum"),
   (Minus,"$difference"),
   (Mult,"$product"),
   (Less,"$less"),
   (Leq,"$lesseq"),
   (Greater,"$greater"),
   (Geq,"$greatereq")
   ]


  
val dcl = [plus_tm,minus_tm,mult_tm,less_tm,leq_tm,greater_tm,geq_tm]

fun is_dc var = 
  (is_member var dcl orelse name_of var = "=") handle _ => false

fun is_dca (term,arity) = 
  (is_dc term andalso arity = 2) orelse (name_of term = "=" andalso arity = 2)

fun is_dcaty ((term,arity),str) = is_dca (term,arity)

(* non linear arithmetic hack *)
val dcl2 = [plus_tm,minus_tm,less_tm,leq_tm,greater_tm,geq_tm]

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