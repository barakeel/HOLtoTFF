signature printresult =
sig

  type term     = Term.term
  type hol_type = Type.hol_type
  type thm      = Thm.thm
  type ppstream = HOLPP.ppstream
  type goal = (Term.term list * Term.term) 
 
  val print_result : ppstream -> thm list -> goal -> goal -> thm -> bool -> unit
  val output_result : string -> thm list -> goal -> goal -> thm -> bool -> unit
  val output_tffpath : string -> string -> unit
  
end