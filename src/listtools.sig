signature listtools =
sig
  
  val is_member : ''a -> ''a list -> bool
  val erase_double : ''a list -> ''a list
  val add_once : ''a -> ''a list -> ''a list
(* dictionnary *)
  val repeatchange : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val add_entry : (''a * 'b) -> (''a * 'b) list -> (''a * 'b) list
  val lookup : ''a -> (''a * 'b) list -> 'b
  val newname : string -> string list -> string
  val addnewnamel : (''a * string) list -> 
                   (''a * string) list -> 
                   (''a * string) list
  
(* condition *)  
  val switch : (bool * 'a) list -> 'a -> 'a
  val switcherr : (bool * 'a) list -> exn -> 'a (* never used *)
  val switcharg : 'a -> (('a -> bool) * 'b) list -> 'b -> 'b
  val switchargerr : 'a -> (('a -> bool) * 'b) list -> exn -> 'b
  
end
