signature blibReader =
sig
  
  include Abbrev
  
  (* reading *)
    (* types *)
  val mk_rtyadict : (('a * 'b) * 'c) list -> ('c * 'a) list
    (* variables *)
  val mk_rvdict :  ('a * 'b) list -> ('a * 'b) list -> ('b * 'a) list
  val read_axioml : string list -> 
                    (string * hol_type) list * 
                    (string * term) list ->
                    term list                     
  val format_proof : string list -> (string * string * int) list
  val read_proof : (string * string * int) list ->
                   (string * hol_type) list * 
                   (string * term) list ->
                   (term * int) list                
  (* proving *)
  val PROVE_GOAL  : goal -> thm
  val PROVE_AXIOM : term list -> term -> thm
  val PROVE_FALSE : thm list -> thm
  val PROVE_PROOF : string -> thm list -> (term * int) list -> thm
  

end