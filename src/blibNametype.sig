signature blibNametype =
sig
  
  include Abbrev
  
  val name_leaftype : hol_type -> string
  val name_simplety : hol_type -> string
  val add_simpletyal :(hol_type * int) list -> 
                      ((hol_type * int) * string) list -> 
                      ((hol_type * int) * string) list
  val add_innersimpletyal : (hol_type * int) list -> 
                            ((hol_type * int) * string) list -> 
                            ((hol_type * int) * string) list
  val add_compoundtyal : (hol_type * int) list -> 
                         ((hol_type * int) * string) list -> 
                         ((hol_type * int) * string) list
  val create_tyadict : term -> ((hol_type * int) * string) list

end