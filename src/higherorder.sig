signature higherorder =
sig

  type term = Term.term

  val firstorderbvl : (term * int) list -> bool  
  val firstorderfvcdcl : (term * int) list -> bool
  val booleaarityl : (term * int) list -> bool
  
end
