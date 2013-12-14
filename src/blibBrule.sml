structure blibBrule :> blibBrule =
struct

open HolKernel Abbrev boolLib numSyntax
     blibBtools

fun BRULE_ERR function message =
  HOL_ERR {origin_structure = "blibBrule",
	         origin_function = function,
           message = message}


fun STRIP_SYM thm = CONV_RULE (STRIP_QUANT_CONV SYM_CONV) thm

fun LIST_PROVE_HYP thml thm =
  case thml of
    [] => thm
  | th :: m => LIST_PROVE_HYP m (PROVE_HYP th thm)  

fun LIST_AP_THM thm terml =
  case terml of
    [] => thm 
  | t :: m => LIST_AP_THM (AP_THM thm t) m 


   
fun EXTL bvl thm =
  case rev bvl of
    [] => thm
  | bv :: m => let val th0 = SPECL bvl thm in
                 EXTL (rev m) ( GENL (rev m) (EXT (GEN bv th0)) )  
               end             

fun REMOVE_DEF def thm = 
  let val th1 = DISCH def thm in
  let val th2 = GEN (lhs def) th1 in
  let val th3 = SPEC (rhs def) th2 in
  let val axiom1 = REFL (rhs def) in
  let val th4 = MP th3 axiom1 in
    th4
  end end end end end

fun REMOVE_DEFL defl thm = repeat_change REMOVE_DEF defl thm


end