signature main =
sig
  type term = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm
  type conv = Term.term -> Thm.thm
  type goal = (Term.term list * Term.term)
  
  val beagleproblemlocation : string
  val testlocation : string

  val main_conv : conv
  val beagle_prepare : thm list -> goal -> goal
  (* doesn't call beagle now *)

end