signature blibName =
sig
  
  include Abbrev
  
  val create_tyadict : term -> ((hol_type * int) * string) list
  val create_bvdict : term -> (term * string) list
  val create_fvdict : term -> (term * string) list
  val create_cdict : term -> (term * string) list
  val create_fvatydict : term -> ((hol_type * int) * string) list -> 
                         ((term * int) * string) list
  val create_catydict : term -> ((hol_type * int) * string) list ->
                        ((term * int) * string) list

end