signature monomorph =
sig

type thm = Thm.thm
type term = Term.term

  val name_of : term -> string
  val monomorph_fvc : thm -> thm -> thm list 
  val monomorph_fvc_l : thm list -> thm -> thm list 
  val monomorph_fvc_l_l : thm list -> thm list -> thm list
  
end