signature printtff =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type
  type thm      = Thm.thm
  type ppstream = HOLPP.ppstream
  
  val bvcounter : int ref
  val printterm : ppstream -> term -> ((term * string) list * (term * string) list * (hol_type * string) list) -> unit
  val printthm : ppstream -> thm -> unit
  val outputtff : string -> thm -> unit

end
