signature extracttype =
sig

  type term     = Term.term
  type hol_type = Type.hol_type

  val alltypel : term list -> hol_type list 
  val alphatypel : term list -> hol_type list
  val simpletypel : term list -> hol_type list

end
