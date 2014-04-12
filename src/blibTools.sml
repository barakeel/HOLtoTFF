structure blibTools :> blibTools =
struct

open HolKernel boolLib

(* FUNCTION *)  
fun inv f a b = f b a
fun adj f a = (a, f a)
fun fst_f f (a,b) = (f a, b)
fun snd_f f (a,b) = (a, f b)

fun success f x = (f x ; true) handle _ => false

fun B_ERR function message =
  HOL_ERR{origin_structure = "blib",
          origin_function = function,
          message = message}

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

(* SET *)
fun merge ll = mk_set (flatten ll)

(* ORDERING *)
fun first_n n l = 
  if n < 0 then raise B_ERR "first_n" "Negative"
  else if n = 0 then []
  else hd l :: (first_n (n-1) (tl l)) handle Empty => []
 
(* DICTIONNARY *)
fun add_entry entry dict = 
  if mem (fst entry) (map fst dict) then dict else entry :: dict

fun new_name name used =    
  let val newname = ref name in
  let val n = ref 0 in
    (while mem (!newname) used do
      (n := (!n) + 1;
       newname := name ^ (Int.toString (!n)))
       ;
       !newname)
  end end

fun inject (key,name) dict =
  let val newname = new_name name (map snd dict) in
    add_entry (key,newname) dict
  end  

fun update_froml f l dict = (* doesn't work when replaced by foldr or foldl *)
  case l of
    [] => dict
  | a :: m => update_froml f m (f a dict)

fun injectl l dict = update_froml inject l dict 

(* FILE MANAGEMENT *)
fun readl path = 
  let
    val file = TextIO.openIn path
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
  
fun appendl path linel =
  let val file = TextIO.openAppend path in 
    (outputl file linel;
     TextIO.closeOut file)
  end  
 
fun writel path linel =
  let val file = TextIO.openOut path in 
    (outputl file linel;
     TextIO.closeOut file)  
  end  

(* SYNTAX *)
fun is_binop term = is_conj term orelse is_disj term orelse is_imp_only term
fun is_unop term = is_neg term
fun is_quant term = is_forall term orelse is_exists term  

fun strip_quant term =
  if is_forall term then strip_forall term
  else if is_exists term then strip_exists term
  else raise B_ERR "strip_quant" "Bad argument"
  
fun find_atoml term =
  if is_quant term then let val (qbvl,t) = strip_quant term in find_atoml t end  
  else if is_binop term then find_atoml (lhand term) @ find_atoml (rand term)
  else if is_unop term then find_atoml (rand term)
  else [term]

fun gen_dest_type ty = if is_vartype ty then (dest_vartype ty,[]) else dest_type ty
  
end
  