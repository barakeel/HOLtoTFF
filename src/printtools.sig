signature printtools =
sig

  include Abbrev
  
  val output_info : string -> string -> unit 
  val output_error : string -> string -> exn
  val pp_conv : ppstream -> string -> thm -> unit
  val pp_open : string -> bool -> (TextIO.outstream * ppstream)

end  