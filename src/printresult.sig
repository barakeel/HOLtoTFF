signature printresult =
sig
  
  include Abbrev
  
  (* path are absolute *)
  val directory : string 
  val mk_holpath : string -> string 
  val mk_tffpath : string -> string 
  val mk_SZSstatuspath : string -> string 
  val mk_resultpath : string -> string 
  val mk_convpath : string -> string 
  val mk_addresspath : unit -> string
  val mk_tffsavepath : string -> string 
  val mk_proofpath : string -> string 
  (* this path is stored in a fix location and will be read by a script *)
  val output_tffgoalpath : string -> unit
  (* result *)
  val output_result : string -> thm list -> goal -> 
                      string -> (bool * string) list -> 
                      unit
  (* conversion *) 
  val outstream_eqth_info : TextIO.outstream -> string -> thm -> unit
  val output_beagle_conv : string -> goal -> unit 

end