signature listtools =
sig
  
  val isempty : 'a list -> bool
  val ismember : ''a -> ''a list -> bool
  val erasedouble : ''a list -> ''a list
(* dictionnary *)
  val fstcomponent : ('a * 'b) list -> 'a list 
  val erase3rdcomponent : ('a * 'b * 'c) list -> ('a * 'b) list
  val erase2ndcomponent : ('a * 'b * 'c) list -> ('a * 'c) list
  val addentry: (''a * 'b) -> (''a * 'b) list -> (''a * 'b) list
  val lookup : ''a -> (''a * 'b) list -> 'b
(* condition *)  
  val switch : (bool * 'a) list -> 'a -> 'a
  val switcherr : (bool * 'a) list -> exn -> 'a (* never used *)
  val switcharg : 'a -> (('a -> bool) * 'b) list -> 'b -> 'b
  val switchargerr : 'a -> (('a -> bool) * 'b) list -> exn -> 'b
  
end
