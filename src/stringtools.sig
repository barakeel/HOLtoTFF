signature stringtools =
sig

  val space : int -> string 
  val indent : int -> string
  val namestrn : string -> int -> string

  val isalphanumor_ : string -> bool
  val islowerword : string -> bool
  val isupperword : string -> bool 

end
