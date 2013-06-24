signature listtools =
sig
  
  val is_empty : 'a list -> bool
  val is_member : ''a -> ''a list -> bool
  val erase_double : ''a list -> ''a list
  val add_once : ''a -> ''a list -> ''a list
(* dictionnary *)
  val fstcomponent : ('a * 'b) list -> 'a list 
  val erase3rdcomponent : ('a * 'b * 'c) list -> ('a * 'b) list
  val erase2ndcomponent : ('a * 'b * 'c) list -> ('a * 'c) list
  val add_entry: (''a * 'b) -> (''a * 'b) list -> (''a * 'b) list
  val lookup : ''a -> (''a * 'b) list -> 'b
(* condition *)  
  val switch : (bool * 'a) list -> 'a -> 'a
  val switcherr : (bool * 'a) list -> exn -> 'a (* never used *)
  val switcharg : 'a -> (('a -> bool) * 'b) list -> 'b -> 'b
  val switchargerr : 'a -> (('a -> bool) * 'b) list -> exn -> 'b
  
end
