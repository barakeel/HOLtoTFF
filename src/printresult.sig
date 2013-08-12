signature printresult =
sig
  
  include Abbrev
  
  (* path are absolute *)
  val directory : string 

  val mk_SZSstatuspath : string -> string 
  val mk_addresspath : unit -> string
  
  val mk_resultpath : string -> string 
  val mk_tffpath : string -> string 
  
  val mk_convpath : string -> string 
  val mk_errpath : string -> string 
  val mk_tfferrpath : string -> string
  val mk_statspath : string -> string
  
  val write_stats : string -> (int * string) -> (int * string) list
                         -> (int * string) list -> unit
  (* this path is stored in a fix location and will be read by a script *)
  val write_tffpath : string -> unit
  (* result *)
  val write_result : string -> thm list -> goal -> 
                      string -> (bool * string) list -> 
                      unit
  (* debugging *)                   
  val write_conv : string -> thm list -> goal -> unit 
  val flags_update_conv : thm list -> goal -> unit
  val write_err : string -> thm list -> goal -> string -> string -> unit
  

end