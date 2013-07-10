signature stringtools =
sig

  val space : int -> string 
  val indent : int -> string
  
  val name_strn : string -> int -> string
  val list_name_str : string -> int -> string list
  
  val is_alphanumor_ : string -> bool
  val is_lowerword : string -> bool
  val is_upperword : string -> bool 
  
 
end
