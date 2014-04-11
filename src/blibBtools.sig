signature blibBtools =
sig
  
(* FUNCTION *)
  val inv : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val fst_f = ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val snd_f = ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val adj : ('a -> 'b) -> 'a -> 'a * 'b 
  val success : ('a -> 'b) -> 'a -> bool
(* ERROR *)
  val wrap :  string -> string -> ('a -> 'b) -> 'a -> 'b
  val B_ERR : string -> string -> exn
(* STRING *)
  val is_alphanumor_ : string -> bool
  val alias : string -> string -> string
  val concats : string -> string list -> string
(* LIST *)
  val mk_list : int -> 'a -> 'a list
  (* set *) 
  val is_member : ''a -> ''a list -> bool
  val is_member_eq : ('a -> 'a -> bool) -> 'a -> 'a list ->  bool
  val erase_double : ''a list -> ''a list
  val erase_double_eq : ('a -> 'a -> bool) -> 'a list -> 'a list
  val inter : ''a list -> ''a list -> ''a list
  val merge : ''a list list -> ''a list
  (* sort *)
  val quicksort : (('a * 'a) -> bool) -> 'a list -> 'a list
  val first_n : int -> 'a list -> 'a list
  (* dictionnary *)
  val add_entry : (''a * 'b) -> (''a * 'b) list -> (''a * 'b) list
  val lookup : ''a -> (''a * 'b) list -> 'b
  val inject : ((''a * string) * (''a * string) list) -> 
                    (''a * string) list 
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

end