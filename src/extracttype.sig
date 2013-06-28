signature extracttype =
sig

  type term     = Term.term
  type hol_type = Type.hol_type
  type VARCAT = mydatatype.VARCAT

  val alltypel : (term * int) list -> (hol_type * int) list
  
  val leafvtypel : (hol_type * int) list -> (hol_type * int) list 
  val alphatypel : (hol_type * int) list  -> (hol_type * int) list 
  val nodevtypel : (hol_type * int) list -> (hol_type * int) list
  
  val dest_type_nb : (hol_type * int) -> ((hol_type * int) list * (hol_type * int))  

end
