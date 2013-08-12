signature printtff =
sig
  
  include Abbrev
  
  val pptff_term : ppstream -> term -> 
                   ((hol_type * int) * string) list *
                   (term * string) list *
                   (term * string) list *
                   (term * string) list ->
                   bool -> 
                   unit

  val pptff_tff : ppstream -> goal -> unit
  val write_tff : string -> goal -> bool -> unit

end