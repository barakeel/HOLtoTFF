signature extracttype =
sig

  type term     = Term.term
  type hol_type = Type.hol_type
  type VARCAT = mydatatype.VARCAT

  val all_tya : term -> (hol_type * int) list
  
  val get_simpletyal : (hol_type * int) list -> (hol_type * int) list 
  val get_compoundtyal : (hol_type * int) list  -> (hol_type * int) list 

  val dest_type_nb : (hol_type * int) -> ((hol_type * int) list * (hol_type * int))  

end
