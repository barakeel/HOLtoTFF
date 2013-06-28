signature namevar =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type

  val name_numeral : term -> string
  val namebvn : term -> int -> string
  val namefvcl : (term * int) list -> (term * int * string) list 
  
end
