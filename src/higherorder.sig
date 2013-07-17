signature higherorder =
sig

  include Abbrev

  val firstorder_bval : (term * int) list -> bool  
  val firstorder_fvcal : (term * int) list -> bool

end
