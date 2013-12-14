signature blibTffsyntax =
sig

  include Abbrev
  
  (* writer *)
  (* hack NLIA *)
  val linearn : term -> bool
  val lineari : term -> bool
  val is_lowerword : string -> bool
  val is_upperword : string -> bool
  val name_tff : string -> term -> string
  (* reader *)
  val is_numword   : string -> bool
  
  
end