signature listtools =
sig

  val ismember : ''a -> ''a list -> bool
  val erasedouble : ''a list -> ''a list
  val lookup : ''a -> (''a * 'b) list -> 'b
  
  val fstcomponent : ('a * 'b) list -> 'a list 
  val erase3rdcomponent : ('a * 'b * 'c) list -> ('a * 'b) list
  val erase2ndcomponent : ('a * 'b * 'c) list -> ('a * 'c) list
  
  val switch : (bool * 'a) list -> 'a -> 'a
  val switcherr : (bool * 'a) list -> exn -> 'a (*never used*)
  val switcharg : 'a -> (('a -> bool) * 'b) list -> 'b -> 'b
  val switchargerr : 'a -> (('a -> bool) * 'b) list -> exn -> 'b
  
end
