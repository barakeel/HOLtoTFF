structure blibFreshvar :> blibFreshvar =
struct

open HolKernel Abbrev boolLib
     blibBtools
     blibSyntax blibExtractvar

fun FRESHVAR_ERR function message =
  HOL_ERR{origin_structure = "blibFreshvar",
          origin_function = function,
          message = message}

(* create namel and varl *)
fun create_intl_aux size = 
  case size of
    0 => []
  | _ => if size < 0 then raise FRESHVAR_ERR "create_intl_aux" "negative number"
         else size :: create_intl_aux (size - 1)
fun create_intl size = rev (create_intl_aux size)

fun prepend str1 str2 = str1 ^ str2

fun mk_namel str size =
  let val intstrl = map Int.toString (create_intl size) in
    map (prepend str) intstrl
  end

fun mk_varl (strl,tyl) = map mk_var (combine (strl,tyl))

(* create a fresh name *)
fun mk_newname name used =    
  let val newname = ref name in
  let val n = ref 0 in
    (
    while is_member (!newname) used do
      (
      n := (!n) + 1;
      newname := name ^ (Int.toString (!n))
      )
    ;
    !newname
    )
  end end

fun mk_newnamel name n used =
  if n = 0 then []
  else if n < 0 then raise FRESHVAR_ERR "create_newnamel" "negative number"
  else 
    let val newname = mk_newname name used in
      newname :: mk_newnamel name (n-1) (newname :: used)
    end
  
(* create a fresh variable *)
fun mk_newvar var used = 
  let val ty = type_of var in
  let val name = fst (dest_var var) in
  let val n = ref 0 in
  let val v = ref (mk_var (name,ty)) in
    (
    while is_member (!v) used do
      ( n := (!n) + 1;
        v :=  mk_var (name ^ (Int.toString (!n)),ty) ) 
    ;
    !v
    )    
  end end end end 
  
fun mk_newvarl varl used =
  case varl of
    [] => []
  | var :: m => let val newv = mk_newvar var used in
                  newv :: mk_newvarl m (newv :: used)
                end  

(* dict *)
fun add_newname (key,name) dict =
  let val newname = mk_newname name (map snd dict) in
    add_entry (key,newname) dict
  end  

fun add_newnamel entry dict = repeat_change add_newname entry dict 


end