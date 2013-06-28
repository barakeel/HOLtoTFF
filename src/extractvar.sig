signature extractvar =
sig

  type term   = Term.term
  type VARCAT = mydatatype.VARCAT
  
  val extract_var : term -> ((term * int) * VARCAT) list 
  val extract_varl : term list -> ((term * int) * VARCAT) list 

(* all this functions are to be called on the result of extract_var or varl *)  
  val erase_bv : ((term * int) * VARCAT) list -> ((term * int) * VARCAT) list
  val erase_number : ((term * int) * VARCAT) list -> ((term * int) * VARCAT) list
  
  val get_bval : ((term * int) * VARCAT) list -> (term * int) list
  val get_fval : ((term * int) * VARCAT) list -> (term * int) list
  val get_cal : ((term * int) * VARCAT) list -> (term * int) list
  val get_fvcal : ((term * int) * VARCAT) list -> (term * int) list
  
  val get_fvcl_thm : thm -> term list
  val get_cl_thm : thm -> term list
  
end
