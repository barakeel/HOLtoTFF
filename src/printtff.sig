signature printtff =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type
  type thm      = Thm.thm

  val bvcounter : int ref
  val printterm : term -> ((term * string) list * (term * string) list * (hol_type * string) list) -> string

  val printthm : thm -> string
  val outputtff : string -> thm -> unit

end
