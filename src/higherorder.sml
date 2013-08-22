structure higherorder :> higherorder =
struct

open HolKernel Abbrev boolLib 
     listtools tools 
     extractvar

fun HIGHERORDER_ERR function message =
  HOL_ERR {origin_structure = "higherorder",
           origin_function = function,
           message = message}

(* tools *)
fun get_lowestarity (term,arity) termal =
  case termal of
    [] => arity
  | (t,a) :: m => if term = t 
                  then 
                    if a < arity 
                    then get_lowestarity (term,a) m
                    else get_lowestarity (term,arity) m 
                  else get_lowestarity (term,arity) m     
  
fun collapse_lowestarity_aux varal varalfix =
  case varal of
    [] => []
  | (var,arity) :: m => 
    let val lowestarity = get_lowestarity (var,arity) varalfix in
      (var,lowestarity) :: collapse_lowestarity_aux m varalfix
    end
fun collapse_lowestarity varal = 
  erase_double (collapse_lowestarity_aux varal varal)

(* VARIABLE *)

(* bound *)
fun firstorder_bval bval =
  case bval of
    [] => true
  | (bv,arity) :: m => 
      if arity = 0
      then firstorder_bval m
      else false

fun firstorder_bval_err bval =
   case bval of
    [] => true
  | (bv,arity) :: m => 
      if arity = 0 
      then firstorder_bval_err m
      else raise HIGHERORDER_ERR "firstorder_bval" (term_to_string bv)

(* free *)
fun firstorder_fval_aux fval fvlal =
  case fval of
    [] => true
  | (fv,arity) :: m => 
      if arity = lookup fv fvlal
      then firstorder_fval_aux m fvlal
      else false                 
fun firstorder_fval fval = 
  firstorder_fval_aux fval (collapse_lowestarity fval)                        

fun firstorder_fval_err_aux fval fvlal =
  case fval of
    [] => true
  | (fv,arity) :: m => 
      if arity = lookup fv fvlal 
      then firstorder_fval_err_aux m fvlal
      else raise HIGHERORDER_ERR "firstorder_fval" (term_to_string fv)                 
fun firstorder_fval_err fval = 
  firstorder_fval_err_aux fval (collapse_lowestarity fval)      

(* constant *)
fun firstorder_cal_aux cal clal =
  case cal of
    [] => true
  | (c,arity) :: m => 
      if arity = lookup c clal
      then firstorder_cal_aux m clal
      else false                 
fun firstorder_cal cal = 
  firstorder_cal_aux cal (collapse_lowestarity cal)      

fun firstorder_cal_err_aux cal clal =
  case cal of
    [] => true
  | (c,arity) :: m => 
      if arity = lookup c clal
      then firstorder_cal_err_aux m clal
      else raise HIGHERORDER_ERR "firstorder_cal" (term_to_string c)                 
fun firstorder_cal_err cal = 
  firstorder_cal_err_aux cal (collapse_lowestarity cal)    

(* term *)
fun firstorder term =
  let 
    val bval = get_bval term
    val fval = get_fval term
    val cal = get_cal term
  in  
   firstorder_bval bval andalso 
   firstorder_fval fval andalso
   firstorder_cal  cal
  end
  
fun firstorder_err term =
  let 
    val bval = get_bval term
    val fval = get_fval term
    val cal = get_cal term
  in  
   firstorder_bval_err bval andalso 
   firstorder_fval_err fval andalso
   firstorder_cal_err (filter is_not_dca cal)
  end  
  
(* goal *)  
fun firstorder_goal goal =
  let val terml = (fst goal) @ [snd goal] in
  let val term = list_mk_conj (terml) in 
    firstorder term
  end end
 
(* thm *)  
fun firstorder_thm thm = firstorder_goal (hyp thm,concl thm)

end
