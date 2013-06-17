signature nametype =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type
  
  val addleafvtypel : (hol_type * int) list -> ((hol_type * int) * string) list -> ((hol_type * int) * string) list
  val addnodevsimpletypel : (hol_type * int) list -> ((hol_type * int) * string) list -> ((hol_type * int) * string) list
  val addnodevtypel : (hol_type * int) list -> ((hol_type * int) * string) list -> ((hol_type * int) * string) list
 
end
