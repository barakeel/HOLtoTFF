signature stringtools =
sig

  val erasechar : string -> string 
  val space : int -> string 
  val indent : int -> string
  
  val isalphanumor_ : string -> bool
  val islowerword : string -> bool
  val isupperword : string -> bool 

end
