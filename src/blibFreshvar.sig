signature blibFreshvar =
sig

  include Abbrev

  val mk_namel : string -> int -> string list
  val mk_varl : (string list * hol_type list) -> term list
(* create a fresh name *)  
  val mk_newname : string -> string list -> string
  val mk_newnamel : string -> int -> string list -> string list
(* create a fresh variable *)
  val mk_newvar : term -> term list -> term 
  val mk_newvarl : term list -> term list -> term list
(* dict *)
  val add_newname : (''a * string) -> (''a * string) list -> 
                    (''a * string) list 
  val add_newnamel : (''a * string) list -> (''a * string) list -> 
                     (''a * string) list  

end
