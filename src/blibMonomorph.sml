structure blibMonomorph :> blibMonomorph =
struct

open HolKernel Abbrev boolLib blibTools blibExtract

(* Test *)
fun is_polymorph term = (polymorphic o type_of) term
fun is_polymorph_thm thm =  exists is_polymorph (get_cl_thm thm)
fun is_polymorph_pb (thml,goal) = exists is_polymorph_thm thml

(* Matching constants *)
fun match_cc c1 c2 = 
  if #Name (dest_thy_const c1) = #Name (dest_thy_const c2) andalso
     #Thy (dest_thy_const c1) = #Thy (dest_thy_const c2)
  then [match_type (type_of c1) (type_of c2)] handle _ => []
  else []

fun substl_clc cl c = (flatten (map (match_cc c) cl))

(* Substitution normalization *)
fun less_redres {redex = r1, residue = _} {redex = r2, residue = _} = 
  (Type.compare (r1,r2) = LESS)
fun normalize_subst subst = sort less_redres (mk_set subst) 
fun normalize_substl substl = mk_set (map normalize_subst substl)

(* One pass monomorphisation of a problem *)
fun monomorph_thm cl thm =
  let val clp = filter is_polymorph (get_cl_thm thm) in
  let val substl = [] :: flatten (map (substl_clc cl) clp) in
    map (inv INST_TYPE thm) (normalize_substl substl)
  end end
 
fun monomorph_pb_one (thml,goal) = 
  let val cl = merge (map get_cl (snd goal :: fst goal) @ map get_cl_thm thml) in
    (flatten (map (monomorph_thm cl) thml), goal)
  end   

(* Main function *) 
fun monomorph_pb_aux mnb (thml,goal) nbinst =
  let val (thml1,goal1) = monomorph_pb_one (thml,goal) in
  let val diff = List.length thml1 - List.length thml in  
  let val n = nbinst + diff in
    if n > mnb orelse diff = 0 
    then (thml,goal) 
    else monomorph_pb_aux mnb (thml1,goal1) n 
  end end end

fun monomorph_pb mnb pb = monomorph_pb_aux mnb pb 0
      
end