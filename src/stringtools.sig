signature stringtools =
sig

  val space : int -> string 
  val indent : int -> string
  
  val last2char : string -> string 
  val erase_last4char : string -> string
  val change_to_predicatety : string -> string
  
  val name_strn : string -> int -> string
  val list_name_str : string -> int -> string list
  
  val is_alphanumor_ : string -> bool
  val is_lowerword : string -> bool
  val is_upperword : string -> bool 
  
end