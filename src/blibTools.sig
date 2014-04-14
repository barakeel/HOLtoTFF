signature blibTools =
sig
  
(* FUNCTION *)
  val inv : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val fst_f : ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val snd_f : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val adj : ('a -> 'b) -> 'a -> 'a * 'b 
(* ERROR *)
  val success : ('a -> 'b) -> 'a -> bool
  val B_ERR : string -> string -> exn
(* STRING *)
  val is_alphanum_ : string -> bool
  val alias : string -> string -> string
  val concats : string -> string list -> string
  val numl : string -> int -> string list
(* LIST *)
  val merge : ''a list list -> ''a list
  val first_n : int -> 'a list -> 'a list
  (* inject dict *)
  val new_name : string -> string list -> string
  val injectl : (''a * string) list -> (''a * string) list -> 
                (''a * string) list
(* FILE MANAGEMENT *)
  val readl : string -> string list
  val writel : string -> string list -> unit
  val appendl : string -> string list -> unit
  
(* SYNTAX *)
  val is_binop : term -> bool 
  val is_unop : term -> bool
  val is_quant : term -> bool 
  val strip_quant : term -> (term list * term)
  val find_atoml : term -> term list 
  val gen_dest_type : hol_type -> string * hol_type list

end