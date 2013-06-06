signature extracttype =
sig

  type term     = Term.term
  type hol_type = Type.hol_type
  type VARCAT = mydatatype.VARCAT

  val alltypel : (term * int * VARCAT) list -> hol_type list 
  val alphatypel : (term * int * VARCAT) list -> hol_type list
 
end
