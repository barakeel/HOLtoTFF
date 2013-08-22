structure freshvar :> freshvar =
struct

open HolKernel Abbrev boolLib
     basictools stringtools listtools
     syntax extractvar

fun FRESHVAR_ERR function message =
    HOL_ERR{origin_structure = "freshvar",
            origin_function = function,
            message = message}

fun create_intl_aux size = 
  case size of
    0 => []
  | _ => if size < 0 then raise FRESHVAR_ERR "create_intl_aux" "negative number"
         else size :: create_intl_aux (size - 1)
fun create_intl size = rev (create_intl_aux size)

fun prepend str1 str2 = str1 ^ str2

fun create_namel str size =
  let val intstrl = map Int.toString (create_intl size) in
    map (prepend str) intstrl
  end

fun list_mk_var (strl,tyl) = map mk_var (combine (strl,tyl))

(* create a fresh name *)
fun create_newname_aux name used =    
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

fun create_newname name term = 
  create_newname_aux name (map name_of (all_var term)) 
 
fun list_create_newname name terml = 
  create_newname_aux name (map name_of (all_varl terml)) 
    
fun create_newname_thm name thm = 
  create_newname_aux name (map name_of (all_var_thm thm))
    
(* create a fresh variable *)
fun create_newvar_aux var used = 
  let val ty = type_of var in
  let val name = fst (dest_var var) in
  let val n = ref 0 in
  let val var = ref (mk_var (name,ty)) in
    (
    while is_member (!var) used do
      ( n := (!n) + 1;
        var :=  mk_var (name ^ (Int.toString (!n)),ty) ) 
    ;
    (!var)
    )    
  end end end end 
  
fun create_newvar var term = create_newvar_aux var (all_var term)  
fun create_newvar_thm var thm = create_newvar_aux var (all_var_thm thm)

fun create_newvarl_aux varl used =
  case varl of
    [] => []
  | v :: m => let val newv = create_newvar_aux v used in
                create_newvar_aux v used :: create_newvarl_aux m (v :: used)
              end  

fun create_newvarl varl term = create_newvarl_aux varl (all_var term)   
fun create_newvarl_thm varl thm = create_newvarl_aux varl (all_var_thm thm)

(* dict *)
fun add_newname (key,name) dict =
  let val newname = create_newname_aux name (map snd dict) in
    add_entry (key,newname) dict
  end  

fun add_newnamel entry dict = repeatchange add_newname entry dict 


end