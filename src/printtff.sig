signature printtff =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type
  type thm      = Thm.thm
  type ppstream = HOLPP.ppstream
  type goal = (term list * term)
  
  val print_term : ppstream -> term -> 
                   ((hol_type * int) * string) list *
                   (term * string) list *
                   (term * string) list *
                   (term * string) list ->
                   bool -> 
                   unit

  val print_tff : ppstream -> goal -> unit
  val output_tff : string ->  goal -> unit

end