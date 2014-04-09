structure blibMonomorph :> blibMonomorph =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype
     blibSyntax
     blibExtractvar blibNamevar

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

fun substl_clc cl c = (List.concat (map (match_cc c) cl))

(* Substitution normalization *)
fun less_ty (ty1,ty2) = (Type.compare (ty1,ty2) = LESS)
fun less_redres ({redex = r1, residue = _},{redex = r2, residue = _}) = less_ty (r1,r2)   
fun normalize_subst subst = quicksort less_redres (erase_double subst) 
fun normalize_substl substl = erase_double (map normalize_subst substl)

(* One pass monomorphisation of a problem *)
fun monomorph_thm cl thm =
  let val clp = filter is_polymorph (get_cl_thm thm) in
  let val substl = [] :: List.concat (map (substl_clc cl) clp) in
    map (inv INST_TYPE thm) (normalize_substl substl)
  end end
 
fun monomorph_pb_one (thml,goal) = 
  let val cl = merge (get_cl_goal goal :: map get_cl_thm thml) in
    (List.concat (map (monomorph_thm cl) thml), goal)
  end   

(* Parameters are 3 iterations and 100 instantiations *)
fun monomorph_pb_aux (thml,goal) nbinst nbiter =
  if nbiter = 3 then (thml,goal) else
    let val (thml1,goal1) = monomorph_pb_one (thml,goal) in
    let val diff = List.length thml1 - List.length thml in  
    let val n = nbinst + diff in
      if n > 100 orelse diff = 0 then (thml,goal)  
      else monomorph_pb_aux (thml1,goal1) n (nbiter + 1)
    end end end
 
(* Main function *) 
fun monomorph_pb pb = wrap "blibMonomorph" "monomorph_pb" "" 
   (monomorph_pb_aux pb 0) 0  
      
end

           