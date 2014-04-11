structure blibBtools :> blibBtools =
struct

open HolKernel boolLib

(* FUNCTION *)  
fun inv f a b = f b a
fun adj f a = (a, f a)

fun fst_f f (a,b) = (f a, b)
fun snd_f f (a,b) = (a, f b)

fun success f x =
  (f x; true) handle _ => false
  
fun wrap f m function x =
  function x               
  handle  
    HOL_ERR {origin_structure = s1, origin_function = f1, message = m1}
      => raise HOL_ERR {origin_structure = s1,
                        origin_function = f ^ " - " ^ f1,
                        message = m ^ " - " ^ m1}           
  | UNCHANGED => raise UNCHANGED
  | _ => raise HOL_ERR {origin_structure = "blib",
                        origin_function = f,
                        message = m}

fun B_ERR function message =
  HOL_ERR{origin_structure = "blib",
          origin_function = function,
          message = message}

(* STRINGTOOOLS *)
fun first_n_char n str = String.substring (str,0,n)
fun rm_first_n_char n str = String.substring (str,n,String.size str - n)

fun last_n_char n str = String.substring (str,String.size str - n,n)
fun rm_last_n_char n str = String.substring (str,0,String.size str - n)

(* include the empty string *)
fun is_alphanum_charl charl= 
  case charl of
    [] => true    
  | a :: m => (Char.isAlphaNum a orelse (Char.toString a) = "_") 
              andalso is_alphanum_charl m  

fun is_alphanum_ str = is_alphanum_charl (explode str)
fun alias str1 str2 = if is_alphanum_ str2 then str2 else str1

fun concats s strl = 
  case strl of
    [] => ""
  | [str] => str
  | str :: m => str ^ s ^ concats s m

(* LIST *) 
fun mk_list n a =
  if n < 0 then raise B_ERR "mk_list" "Negative"
  else
    case n of 
      0 => []
    | _ => a :: mk_list (n -1) a


(* SET *)
fun is_member_eq eq elem list  = exists (eq elem) list
fun erase_double_eq eq list  =
  case list of
   [] => []
 | a :: m => if is_member_eq eq a m 
             then erase_double_eq eq m 
             else a :: erase_double_eq eq m

fun is_member elem list = is_member_eq equal elem list 
fun erase_double list = erase_double_eq equal list 

fun inter l1 l2 = filter (inv is_member (erase_double l2)) (erase_double l1) 
fun merge ll = erase_double (List.concat ll)

(* ORDERING *)
fun quicksort << xs = let
  fun qs [] = []
    | qs [x] = [x]
    | qs (p::xs) = let
        val lessThanP = (fn x => << (x, p))
        in
          qs (filter lessThanP xs) @ p :: (qs (filter (not o lessThanP) xs))
        end
  in
    qs xs
  end

fun first_n n l = 
  if n < 0 then raise B_ERR "first_n" "Negative"
  else if n = 0 then []
  else hd l :: (first_n (n-1) (tl l)) handle Empty => []
 
(* DICTIONNARY *)
fun add_entry entry dict = 
  if is_member (fst entry) (map fst dict) then dict else entry :: dict

fun lookup elem l =
  case l of 
    []         => (elem; raise B_ERR "lookup" "")
  | (a,b) :: m =>  if a = elem then b else lookup elem m

fun new_name name used =    
  let val newname = ref name in
  let val n = ref 0 in
    (while is_member (!newname) used do
      (n := (!n) + 1;
       newname := name ^ (Int.toString (!n)))
     ;
     !newname)
  end end

fun inject ((key,name),dict) =
  let val newname = new_name name (map snd dict) in
    add_entry (key,newname) dict
  end  

fun injectl l dict = List.foldl inject l dict 



(* FILE MANAGEMENT *)
fun readl filepath = 
  let
    val file = TextIO.openIn filepath
    fun loop file =
      case TextIO.inputLine file of
        SOME line => line :: loop file
      | NONE      => []
  in
    loop file before TextIO.closeIn file
  end 
  
fun outputl file linel =
  case linel of
    [] => ()
  | line :: m => (TextIO.output (file,line ^ "\n"); outputl file m) 
  
fun appendl filepath linel =
  let val file = TextIO.openAppend filepath in 
    (outputl file linel;
     TextIO.closeOut file)
  end  
 
fun writel filepath linel =
  let val file = TextIO.openOut filepath in 
    (outputl file linel;
     TextIO.closeOut file)  
  end  

(* SYNTAX *)
fun is_binop term = 
  is_eq term orelse is_conj term orelse is_disj term orelse is_imp_only term
fun is_unop term = is_neg term
fun is_quant term = is_forall term orelse is_exists term  

fun strip_quant term =
  if is_forall term then strip_forall term
  else if is_exists term then strip_exists term
  else raise B_ERR "strip_quant" "Bad argument"
 
fun find_atoml term =
  if is_quant term then find_atoml_quant term
  else if is_binop term then find_atoml_binop term
  else if is_unop term then find_atoml_unop term
  else [term]
and find_atoml_quant term =
  let val (qbvl,t) = strip_quant term in find_atoml t end  
and find_atoml_binop term = find_atoml (lhand term) @ find_atoml (rand term)
and find_atoml_unop term = find_atoml (rand term)

end
  