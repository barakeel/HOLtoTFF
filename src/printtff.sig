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
                   (term * string) list
                   -> unit
  (* tools *)

  (* *)
  val print_fvctyl : ppstream -> 
                     (term * int) list ->
                     (term * string) list ->
                     ((hol_type * int) * string) list ->
                     unit  
  val print_pb : ppstream -> term -> unit
  val output_tff : string -> term -> unit

end