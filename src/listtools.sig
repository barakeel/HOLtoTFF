signature listtools =
sig

  val make_list_n : int -> 'a -> 'a list
  (* arithmetic *)
  val suml : int list -> int
  val multl : int list -> int list -> int list
  (* set *) 
  val is_member : ''a -> ''a list -> bool
  val is_member_eq : ('a -> 'a -> bool) -> 'a -> 'a list ->  bool
  val erase_double : ''a list -> ''a list
  val erase_double_eq : ('a -> 'a -> bool) -> 'a list -> 'a list
  val add_once : ''a -> ''a list -> ''a list
  val inter : ''a list -> ''a list -> ''a list
  val subset : ''a list -> ''a list -> bool
  val strict_subset : ''a list -> ''a list -> bool 
  val is_maxset : ''a list -> ''a list list -> bool
  val list_subset : ''a list list -> ''a list list -> bool
  val list_merge : ''a list list -> ''a list
  (* sort *)
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