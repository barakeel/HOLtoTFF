signature printtff =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type
  type thm      = Thm.thm
  type ppstream = HOLPP.ppstream
  
  val print_term : ppstream -> term -> 
                   ((hol_type * int) * string) list *
                   (term * string) list *
                   (term * string) list *
                   (term * string) list ->
                   bool -> 
                   unit

  val print_thm : ppstream -> thm -> unit
  val output_tff : string -> thm -> unit

end