signature listtools =
sig

  val ismember : ''a -> ''a list -> bool
  val erasedouble : ''a list -> ''a list
  val map : ''a -> (''a * 'b) list -> 'b
  val fstcomponent : ('a * 'b) list -> 'a list 

  val switch : (bool * 'a) list -> 'a -> 'a
  val switcherr : (bool * 'a) list -> exn -> 'a (*never used*)
  val switcharg : 'a -> (('a -> bool) * 'b) list -> 'b -> 'b
  val switchargerr : 'a -> (('a -> bool) * 'b) list -> exn -> 'b
  
end
