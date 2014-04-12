signature blibPrinter =
sig
  
  include Abbrev
  val write_tff : string -> goal -> unit
  val write_fof : string -> goal -> unit

end