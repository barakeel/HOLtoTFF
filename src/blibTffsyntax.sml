structure blibTffsyntax :> blibTffsyntax =
struct

open HolKernel Abbrev boolLib numSyntax
     blibBtools blibDatatype
     blibSyntax
     
fun TFFSYNTAX_ERR function message =
  HOL_ERR {origin_structure = "blibTffsyntax",
           origin_function = function,
           message = message}


(* VAR NAME *)
fun name_tff str var =
  let val name = name_of var in 
    if is_alphanumor_ name then str ^ name else str
  end
  
(* DEFINED TFF CONSTANTS *)
(* (* bad hack NLIA *) prevent from adding  "*" *)
val dcl = ["=","+","-","*","<","<=",">",">="]
val dcl2 = ["=","+","-","<","<=",">",">="]

val dcdict = [
   (Eq,"$equal"),
   (Add,"$sum"),
   (Minus,"$difference"),
   (Mult,"$product"),
   (Less,"$less"),
   (Leq,"$lesseq"),
   (Greater,"$greater"),
   (Geq,"$greatereq")
   ]
   
fun is_dc var = (is_member (name_of var)) dcl2 handle _ => false
fun is_dca (term,arity) = is_dc term andalso arity = 2
fun is_dcaty ((term,arity),str) = is_dca (term,arity)
  
(* DEFINED TFF TYPES *) (* all types starting with "$" *)
fun is_dtyname name = (substring (name,0,1) = "$")
fun has_not_dtyname ((ty,arity),name) = (not o is_dtyname) name  
fun erase_dtyname tyadict = filter has_not_dtyname tyadict
    

end