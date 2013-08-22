signature extracttype =
sig

  include Abbrev
 
  val all_type : term -> hol_type list
  val all_subtype : term -> hol_type list
  val all_leaftype : term -> hol_type list
  val all_vartype : term -> hol_type list
  (* with arity *)
  val all_tya : term -> (hol_type * int) list
  val get_simpletyal : term -> (hol_type * int) list 
  val get_compoundtyal : term -> (hol_type * int) list 
  val strip_tya : (hol_type * int) -> ((hol_type * int) list * (hol_type * int))  

end
