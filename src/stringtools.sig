signature stringtools =
sig

  val space : int -> string 
  val indent : int -> string
  val name_strn : string -> int -> string

  val is_alphanumor_ : string -> bool
  val islowerword : string -> bool
  val isupperword : string -> bool 

end
