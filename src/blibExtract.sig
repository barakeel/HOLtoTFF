signature blibExtract =
sig

  include Abbrev
  
  val get_fval : term -> (term * int) list 
  val get_cal : term -> (term * int) list 
  val get_fvcal : term -> (term * int) list 
  val get_bvl  : term -> term list
  val get_cl   : term -> term list
  val get_cl_thm   : thm -> term list
  val get_tyal : term -> (hol_type * int) list
  val strip_type_n : (hol_type * int) -> (hol_type * int) list * (hol_type * int)

end