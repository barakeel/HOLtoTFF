signature blibReader =
sig
  
  include Abbrev
 
  (* dictionnaries *)
  val mk_rdict : ((hol_type * int) * string) list *
                 (term * string) list *
                 (term * string) list *
                 (term * string) list ->
                 (string * hol_type) list * (string * term) list
  (* reading *)
  val read_axioml : string list -> 
                    (string * hol_type) list * 
                    (string * term) list ->
                    term list                     
  val format_proof : string list -> (string * string * int) list
  val read_infl : (string * string * int) list ->
                   (string * hol_type) list * 
                   (string * term) list ->
                   (term * int) list                
  (* proving *)
  val PROVE_STEP  : goal -> thm
  val PROVE_AXIOM : term list -> term -> thm
  val PROVE_FALSE : thm list -> thm
  val PROVE_PROOF : string -> thm list -> (term * int) list -> thm
  

end