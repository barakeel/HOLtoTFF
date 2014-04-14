signature blibName =
sig
  
  include Abbrev
  
  val create_tyadict : term -> ((hol_type * int) * string) list
  val create_bvdict : term -> (term * string) list
  val create_cadict : term -> ((term * int) * string) list

end