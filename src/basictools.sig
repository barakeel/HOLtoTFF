signature basictools =
sig
  
  (* function *)
  val inv :('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val repeat_n_fun :  int -> ('a -> 'a) -> 'a -> 'a
  (* error handling *)
  val success : ('a -> 'b) -> 'a -> bool
  val wrap : string -> string -> string -> ('a -> 'b) -> 'a -> 'b 
  
end