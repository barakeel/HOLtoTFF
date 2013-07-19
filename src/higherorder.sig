signature higherorder =
sig

  include Abbrev

  val firstorder_bval : (term * int) list -> bool  
  val firstorder_fvcal : (term * int) list -> bool            
  val firstorder : term -> bool 
  val firstorder_goal : goal -> bool
  val firstorder_thm : thm -> bool 


end