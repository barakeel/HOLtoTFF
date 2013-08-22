signature listtools =
sig
  (* basic tools *)
  val inv :('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  
  val is_member : ''a -> ''a list -> bool
  val is_member_eq : ('a -> 'a -> bool) -> 'a -> 'a list ->  bool
  
  val erase_double : ''a list -> ''a list
  val erase_double_eq : ('a -> 'a -> bool) -> 'a list -> 'a list
  val add_once : ''a -> ''a list -> ''a list
  val inter : ''a list -> ''a list -> ''a list
  val list_merge : ''a list list -> ''a list
  
  val quicksort : (('a * 'a) -> bool) -> 'a list -> 'a list
(* dictionnary *)
  val repeatchange : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val add_entry : (''a * 'b) -> (''a * 'b) list -> (''a * 'b) list
  val lookup : ''a -> (''a * 'b) list -> 'b
(* condition *)  
  val switch : (bool * 'a) list -> 'a -> 'a
  val switcherr : (bool * 'a) list -> exn -> 'a (* never used *)
  val switcharg : 'a -> (('a -> bool) * 'b) list -> 'b -> 'b
  val switchargerr : 'a -> (('a -> bool) * 'b) list -> exn -> 'b
  
end