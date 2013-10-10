signature blibTffsyntax =
sig

  include Abbrev
  
  (* test *)
  val is_lowerword : string -> bool
  val is_upperword : string -> bool
  val is_numword   : string -> bool
  val is_defword   : string -> bool
  (* var *)
  val name_tff : string -> term -> string
  (* constants *)
  val rdcdict: (string * term) list
  val dcprintdict : (blibDatatype.TERMARITH * string) list
  val is_dc : term -> bool
  val is_dca : (term * int) -> bool
  val is_dcaty2 : ((term * int) * string) -> bool
  
  (* type *)
  val erase_dtyname : (('a * 'b) * string) list -> (('a * 'b) * string) list

end