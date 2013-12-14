signature blibBtools =
sig
  
(* FUNCTION *)
  val inv :('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val repeat_change : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  (* error *)
  val success : ('a -> 'b) -> 'a -> bool
  val wrap : string -> string -> string -> ('a -> 'b) -> 'a -> 'b

(* STRING *)
  val space : int -> string 
  val indent : int -> string
  val first_n_char : int -> string -> string
  val rm_first_n_char : int -> string -> string
  val last_n_char : int -> string -> string
  val rm_last_n_char : int -> string -> string
 
  val char_place : string -> string -> int 
  val char_in : string -> string -> bool
  
  val name_strn : string -> int -> string
  val list_name_str : string -> int -> string list
  
  val is_alphanumor_charl : Char.char list -> bool
  val is_alphanumor_ : string -> bool
  val string_to_int : string -> int
  
(* LIST *)
  val mk_list : int -> 'a -> 'a list
  (* arithmetic *)
  val suml : int list -> int
  (* set *) 
  val is_member : ''a -> ''a list -> bool
  val is_member_eq : ('a -> 'a -> bool) -> 'a -> 'a list ->  bool
  val erase_double : ''a list -> ''a list
  val erase_double_eq : ('a -> 'a -> bool) -> 'a list -> 'a list
  val add_once : ''a -> ''a list -> ''a list
  val inter : ''a list -> ''a list -> ''a list
  val substract : ''a list -> ''a list -> ''a list
  val subset : ''a list -> ''a list -> bool
  val strict_subset : ''a list -> ''a list -> bool 
  val is_maxset : ''a list -> ''a list list -> bool
  val list_subset : ''a list list -> ''a list list -> bool
  val merge : ''a list list -> ''a list
  (* sort *)
  val quicksort : (('a * 'a) -> bool) -> 'a list -> 'a list
  (* dictionnary *)
  val add_entry : (''a * 'b) -> (''a * 'b) list -> (''a * 'b) list
  val lookup : ''a -> (''a * 'b) list -> 'b
  (* condition *)  
  val switch : (bool * 'a) list -> 'a -> 'a
  val switcherr : (bool * 'a) list -> exn -> 'a 
  val switcharg : 'a -> (('a -> bool) * 'b) list -> 'b -> 'b
  val switchargerr : 'a -> (('a -> bool) * 'b) list -> exn -> 'b

(* FILE MANAGEMENT *)
  val readl : string -> string list
  val writel : string -> string list -> unit
  val appendl : string -> string list -> unit
  
  
end