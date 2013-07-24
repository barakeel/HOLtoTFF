signature printresult =
sig

  include Abbrev
 
  val print_problem : ppstream -> thm list -> goal -> thm -> bool -> unit
  val output_result : string -> thm list -> goal -> thm -> bool -> unit
  val output_tffpath : string -> unit
  
end