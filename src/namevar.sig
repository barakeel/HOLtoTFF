signature namevar =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type

  val create_bvdict : term -> (term * string) list
  val create_fvdict : term -> (term * string) list
  val create_cdict : term -> (term * string) list
  val create_bvatydict : term -> ((hol_type * int) * string) list -> 
                         ((term * int) * string) list
  val create_fvatydict : term -> ((hol_type * int) * string) list -> 
                         ((term * int) * string) list
  val create_catydict : term -> ((hol_type * int) * string) list ->
                        ((term * int) * string) list
end