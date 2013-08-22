signature tffsyntax =
sig

  include Abbrev
  
  (* var *)
  val name_tff : string -> term -> string
  (* constants *)
  val dcdict : (mydatatype.NODECONST * string) list
  val is_dc : term -> bool
  val is_dca : (term * int) -> bool
  val is_dcaty : ((term * int) * string) -> bool
  
  (* type *)
  val erase_dtyname : (('a * 'b) * string) list -> (('a * 'b) * string) list
  val has_not_dtyname : ('a * 'b) * string -> bool
  val is_dtyname: string -> bool

end