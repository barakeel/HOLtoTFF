signature printtools =
sig

  include Abbrev
  
  val open_file : string -> bool -> TextIO.outstream
  val outstream_eqth : TextIO.outstream -> string -> thm -> unit
  val output_info : string -> string -> unit 
  val output_error : string -> string -> exn




end  