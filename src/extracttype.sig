signature extracttype =
sig

  type term     = Term.term
  type hol_type = Type.hol_type
  type VARCAT = mydatatype.VARCAT

  val all_tya : term -> (hol_type * int) list
  val get_simpletyal : term -> (hol_type * int) list 
  val get_compoundtyal : term -> (hol_type * int) list 

  val strip_type_n : (hol_type * int) -> ((hol_type * int) list * (hol_type * int))  

end
