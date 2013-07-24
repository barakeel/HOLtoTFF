signature namevar =
sig
  
  include Abbrev

  val create_newname : string -> term -> string
  val create_newname_thm : string -> thm -> string 
  val create_newvar : term -> term -> term
  val create_newvar_thm : term -> thm -> term
  val create_newvarl : term list -> term -> term list
  val create_newvarl_thm : term list -> thm -> term list
  
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