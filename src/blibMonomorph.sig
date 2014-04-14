signature blibMonomorph =
sig

  include Abbrev
  
  (* test *)
  val is_polymorph : term -> bool
  val is_polymorph_thm : thm -> bool
  val is_polymorph_pb : thm list * goal -> bool 
  (* monomorphisation *)
  val monomorph_pb : thm list * goal -> thm list * goal
 
end