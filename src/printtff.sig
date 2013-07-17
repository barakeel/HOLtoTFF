signature printtff =
sig
  
  include Abbrev
  
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