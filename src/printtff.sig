signature printtff =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type
  type thm      = Thm.thm
  type ppstream = HOLPP.ppstream
  
  val bvcounter : int ref
  val printterm : ppstream -> term -> ((term * string) list * (term * string) list * ((hol_type * int) * string) list) -> unit
  (* tools *)
  val erasedefinedtype : ((hol_type * int) * string) list -> ((hol_type * int) * string) list 
  val nameaxioml : term list -> (term * string) list
  (* *)
  val printthm : ppstream -> thm -> unit
  val outputtff : string -> thm -> unit

end



  
