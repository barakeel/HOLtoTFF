structure higherorder :> higherorder =
struct

open HolKernel Abbrev boolLib 
     listtools tools 
     extractvar

fun HIGHERORDER_ERR function message =
  HOL_ERR {origin_structure = "higherorder",
           origin_function = function,
           message = message}

(* VARIABLE *)
fun firstorder_bval bval =
  case bval of
    [] => true
  | (bv,arity) :: m => 
    if arity = 0
    then firstorder_bval m
    else false

fun firstorder_fvcal_aux fvcal fvclal =
  case fvcal of
    [] => true
  | (fvc,arity) :: m => 
    if arity = lookup fvc fvclal
    then firstorder_fvcal_aux m fvclal
    else false
                  
fun firstorder_fvcal fvcal = 
  firstorder_fvcal_aux fvcal (collapse_lowestarity fvcal)                        

fun firstorder term =
  let 
    val bval = get_bval term
    val fvcal = get_fvcal term
  in  
   firstorder_bval bval andalso firstorder_fvcal fvcal
  end
  
fun firstorder_goal goal =
  let val terml = (fst goal) @ [snd goal] in
  let val term = list_mk_conj (terml) in 
    firstorder term
  end end
  
fun firstorder_thm thm = firstorder_goal (hyp thm,concl thm)

end
