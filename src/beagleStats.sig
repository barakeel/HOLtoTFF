signature beagleStats =
sig

  include Abbrev
    
  val mflag    : (bool * string) ref 
  val fixpflag : (bool * string) ref 
  val funflag  : (bool * string) ref 
  val boolflag : (bool * string) ref 
  val numflag  : (bool * string) ref 
  val hoflag   : (bool * string) ref 
  val proofflag : (bool * string) ref
  val metisflag : (bool * string) ref 
  val allflag  : ((bool * string) ref) list
  val reset_allflag : unit -> unit 
  val allflag_value : unit -> (bool * string) list  
   
  val flag_on  : (bool * string) ref -> unit 
  val flag_off : (bool * string) ref -> unit 
  val flag_update : (bool * string) ref -> bool -> unit
  val flag_update_metis : thm list -> goal -> unit
  
  (* counter for stats *)
  val nb_problem : (int * string) ref 
  val nb_fixp    : (int * string) ref
  val nb_m       : (int * string) ref
  val nb_fun     : (int * string) ref
  val nb_bool    : (int * string) ref
  val nb_num     : (int * string) ref
  val nb_ho      : (int * string) ref
  val nb_proof   : (int * string) ref
  val nb_metis   : (int * string) ref
  val nb_list1   : ((int * string) ref) list
  
  val nb_unsat   : (int * string) ref
  val nb_unknown : (int * string) ref
  val nb_sat     : (int * string) ref
  val nb_timeout : (int * string) ref
  val nb_parsing : (int * string) ref
  val nb_codeerr : (int * string) ref
  val nb_beagerr : (int * string) ref
  val nb_list2   : ((int * string) ref) list
  
  val nb_all     : ((int * string) ref) list
  
  val update_nb_flag  : (int * string) ref -> (bool * string) ref -> unit
  val addone_nb       : (int * string) ref -> unit

  val update_nbl1 : unit -> unit 
  val update_nbl2 : string -> unit 
  val update_all_nb : string -> unit
  
 

end  