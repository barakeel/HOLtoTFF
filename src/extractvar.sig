signature extractvar =
sig

  type term   = Term.term
  type VARCAT = mydatatype.VARCAT
  
  val extractvar : term -> ((term * int) * VARCAT) list 
  val extractvarl : term list -> ((term * int) * VARCAT) list 

(* all this functions are to be called on the result of extractvarl *)  
  val erase_bv : ((term * int) * VARCAT) list -> ((term * int) * VARCAT) list
  val erase_number : ((term * int) * VARCAT) list -> ((term * int) * VARCAT) list
  
  val get_bval : ((term * int) * VARCAT) list -> (term * int) list
  val get_fvcal : ((term * int) * VARCAT) list -> (term * int) list
  val get_fvcl_thm : thm -> term list
end
