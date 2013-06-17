signature extractvar =
sig

  type term   = Term.term
  type VARCAT = mydatatype.VARCAT
  
  val extractvar : term -> (term * int * VARCAT) list 
  val extractvarl : term list -> (term * int * VARCAT) list 

(* all this functions are to be called on the result of extractvarl *)  
  val erasebv : (term * int * VARCAT) list -> (term * int * VARCAT) list
  val erasenumber : (term * int * VARCAT) list -> (term * int * VARCAT) list
  
  val getbvnargl : (term * int * VARCAT) list -> (term * int) list
  val getfvcnargl : (term * int * VARCAT) list -> (term * int) list

end
