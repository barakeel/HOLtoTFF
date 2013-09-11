signature blibFreshvar =
sig

  include Abbrev

  val create_namel : string -> int -> string list
  val list_mk_var : (string list * hol_type list) -> term list
(* create a fresh name *)  
  val create_newname_aux : string -> string list -> string
  val create_newname : string -> term -> string
  val list_create_newname : string -> term list -> string
  val create_newname_thm : string -> thm -> string 
(* create a fresh variable *)
  val create_newvar_aux : term -> term list -> term 
  val create_newvar : term -> term -> term
  val create_newvar_thm : term -> thm -> term
  val create_newvarl : term list -> term -> term list
  val create_newvarl_thm : term list -> thm -> term list
(* dict *)
  val add_newname : (''a * string) -> (''a * string) list -> 
                    (''a * string) list 
  val add_newnamel : (''a * string) list -> (''a * string) list -> 
                     (''a * string) list  

end
