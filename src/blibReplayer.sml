structure blibReplayer (* :> blibReplayer *) =
struct

open HolKernel Abbrev boolLib numSyntax 
     blibDatatype blibBtools blibBrule blibBtactic
     blibSyntax blibTffsyntax blibFreshvar blibExtractvar
     blibReader blibTactic
     
fun REPLAYER_ERR function message =
  HOL_ERR{origin_structure = "blibReplayer",
          origin_function = function,
          message = message}


fun cooper_goal_aux goal = 
  [CONV_RULE normalForms.CNF_CONV ((#2 (Cooper.COOPER_TAC goal)) [])]
  handle _ => []  

(* INFERING ARITHMETIC THEOREMS *)
(* tools *)
fun multone a l = 
  let fun append l1 l2 = l1 @ l2 in
    map (append a) l
  end
  
fun multl l1 l2 = 
  case l1 of
    [] => []
  | a :: m => multone a l2 @ multl m l2
   
fun list_multl lll = 
  case lll of
    [] => raise REPLAYER_ERR "list_multl" "empty list"
  | [l1] => l1
  | l1 :: m => multl l1 (list_multl m)
  
(* test 
list_multl [[[1],[2]], [[3],[4]]];
*)
 
(* substitution only first order variables*)
fun mk_subst_onebv atom niatoml bv1 =
  let val ty = type_of bv1 in
  let fun is_interesting term = 
    if null (snd (dest_type ty))
    then (type_of term = ty)
    else (((is_var term) orelse (is_const term)) andalso type_of term = ty)
  in
  let val terml = merge_aconv (map (find_terms is_interesting) niatoml) in
  let fun mk_substl bv1 terml = 
    case terml of
      [] => []
    | term :: m => [{redex = bv1, residue = term}] :: mk_substl bv1 m
  in
    mk_substl bv1 terml
  end end end end


fun mk_substl_allbvl atom niatoml bvl = 
  if null bvl then raise REPLAYER_ERR "mk_substl_allbvl" "empty list"
  else list_multl (map (mk_subst_onebv atom niatoml) bvl)
  

fun is_arithpred atom =
  is_eq atom orelse intSyntax.is_less atom orelse intSyntax.is_leq atom orelse
  intSyntax.is_great atom orelse intSyntax.is_geq atom
(* Instantiation *)


fun rm_coeff term = 
  if intSyntax.is_mult term 
  then
    let val (t1,t2) = intSyntax.dest_mult term in
      if intSyntax.is_int_literal t1 then t2 else term
    end
  else term
  
fun get_terml_plus term =
  let val terml1 = intSyntax.strip_plus term in
    map rm_coeff terml1
  end

fun get_terml_atom atom =  
  let val terml1 = if is_arithpred atom then [lhand atom,rand atom]
                   else [atom]
  in
    merge (map get_terml_plus)
  end 
 
(* should remember if instantiation to a quantified variable *)
fun match_term_terml bvl1 term1 terml2 =
  map (Term.match_term term1) terml2

fun match_terml_terml bvl1 term1 terml1 =
  

fun have_same_arithpred 

fun instantiate_unit (bvl1,atom1) (bvl2,atom2)  =
  if have_same_arithpred
  
  if null bvl1 then [(bvl1,atom1)]
  else 
    let val terml1 = get_terml_atom atom1 in
    let val terml2 = get_terml_atom atom2 in
      
      
       
    
    mk_substl_allbvl atom niatoml bvl in
    let val atoml = erase_aconv (map (inv Term.subst atom) substl) in
      atoml
    end end

fun instantiate_unitl unitl niatoml = 
  merge_aconv (map (inv instantiate_unit niatoml) unitl)

(* *)
  
(* Atom list creation *)
(* tools *)
fun mk_preunit bvl term = 
  let val fvcl = get_fvcl term in
    list_mk_forall (inter bvl fvcl,term)
  end
  
fun get_preunitl_clause clause =
  let val (bvl,disj) = strip_forall clause in
  let val terml = strip_disj disj in
    map (mk_preunit bvl) terml
  end end
   
fun get_unitl_clausel clausel = 
  map strip_forall (merge_aconv (map get_preunitl_clause clausel))

(* main *)
fun mk_atoml_clausel clausel = 
  let val unitl = get_unitl_clausel clausel in
  let val rwunitl = rewrite_unitl unitl clausel in
  let val iatoml = instantiate_unitl rwunitl (map snd unitl) in
    iatoml
  end end end


(* Normalisation *)
fun remove_neg atom =
  if is_neg atom then dest_neg atom else atom
 
fun find_normthml_term term =
  let val th1 = QCONV
    (
    OmegaMath.sum_normalise THENC
    (ONCE_REWRITE_CONV [integerTheory.INT_MUL_LID]) THENC
    (ONCE_REWRITE_CONV [STRIP_SYM integerTheory.INT_NEG_MINUS1]) THENC
    REWRITE_CONV [integerTheory.INT_ADD_LID, integerTheory.INT_ADD_RID]
    )
    term
  in
  let val newthl1 = if lhs (concl th1) = rhs (concl th1) then [] else [th1] in
    newthl1
  end end
  handle _ => []

fun find_normthml atom =
  if (is_eq atom orelse intSyntax.is_less atom orelse intSyntax.is_leq atom orelse
     intSyntax.is_great atom orelse intSyntax.is_geq atom)
  then
     find_normthml_term (lhand atom) @ find_normthml_term (rand atom)
  else
    []


(* Simplification *)
(* tools *)
fun remove_one el l1 =
  case l1 of
    [] => []
  | a :: m => if a = el then m else a :: remove_one el m
            
fun elim_same l1 l2 =
  if null (inter l1 l2) 
  then (l1,l2)
  else let val a = hd (inter l1 l2) in
         elim_same (remove_one a l1) (remove_one a l2)
       end
(**)
fun simplify_thm thm =
  let val term = concl thm in
  if type_of (lhand term) = ``:int``
  then
    let val terml1 = intSyntax.strip_plus (lhand term) in
    let val terml2 = intSyntax.strip_plus (rand term) in
    let val (l1,l2) = elim_same terml1 terml2 in
    let val newl1 = quicksort less_term l1 in
    let val newl2 = quicksort less_term l2 in
    let val newterm1 = if null newl1 then ``0:int`` 
                       else intSyntax.list_mk_plus newl1 in
    let val newterm2 = if null newl2 then ``0:int`` 
                       else intSyntax.list_mk_plus newl2 in
      if less_term (newterm1,newterm2)
      then Cooper.COOPER_PROVE (mk_eq (newterm1,newterm2))
      else Cooper.COOPER_PROVE (mk_eq (newterm2,newterm1))
    end end end end end
    end end
  else thm
  end
  

  
fun int_normalize term = rhs (concl (QCONV int_normatom_conv term)) 
                 
fun is_aconv_thm th1 th2 = aconv (concl th1) (concl th2)
fun is_trivial_thm thm = (concl thm = T) orelse concl thm = ``(0:int)=(0:int)``
fun inv_neg atom =
  if is_neg atom then dest_neg atom else mk_neg atom

fun erase_aconv_axiom thml =
  case thml of
    [] => [] 
  | thm :: m => if exists (is_aconv_thm thm) m orelse is_trivial_thm thm
                then erase_aconv_axiom m
                else thm :: erase_aconv_axiom m


(* atom *)
fun mk_bcooperthml_oneatom atom =
  let val goal1 = ([],atom) in
  let val goal2 = ([],mk_neg atom) in
  let val thml1 = cooper_goal_aux goal1 in
  let val thml2 = cooper_goal_aux goal2 in
  let val thml3 = thml1 @ thml2 in
    if null thml3 then ([atom],thml3) else ([],thml3)
  end end end end end
  
fun mk_bcooperthml_atom atom1 atom2 =
  let val newatom1 = 
    if Term.compare (atom1,atom2) = GREATER then atom2 else atom1
  in
  let val newatom2 =
    if Term.compare (atom1,atom2) = GREATER then atom1 else atom2
  in
  let val goal1 = ([],mk_disj (newatom1,newatom2)) in
  let val goal2 = ([],mk_disj (mk_neg newatom1,newatom2)) in
  let val goal3 = ([],mk_disj (mk_neg newatom2,newatom1)) in
  let val goal4 = ([],mk_disj (mk_neg newatom1,mk_neg newatom2)) in
  let val thml1 = cooper_goal_aux goal1 in
  let val thml2 = cooper_goal_aux goal2 in
  let val thml3 = cooper_goal_aux goal3 in
  let val thml4 = cooper_goal_aux goal4 in
    thml1 @ thml2 @ thml3 @ thml4
  end end end end end 
  end end end end end


(* atoml *)                
fun mk_bcooperthml_atoml_aux atoml =
  case atoml of
    [] => []
  | atom :: m => (List.concat (map (mk_bcooperthml_atom atom) m) @
                  mk_bcooperthml_atoml_aux m)

fun mk_bcooperthml_atoml atoml = erase_aconv_axiom (mk_bcooperthml_atoml_aux atoml)
  
(* proof *)
fun is_boolean term = (term = T) orelse (term = F)

fun get_atomlthml_proof_goal proof goal =
  let val terml = (fst goal) in
  let val atoml1 = mk_atoml_clausel (terml) in
  let val atoml11 = filter (not o is_boolean) atoml1 in
  let val atoml2 = map remove_neg atoml11 in
  let val atoml3 = erase_aconv (map int_normalize atoml2) in 
  let val atomlthmll = map mk_bcooperthml_oneatom atoml3 in
  let val atoml4 = merge_aconv (map fst atomlthmll) in
  let val thl1 = erase_aconv_axiom (List.concat (map snd atomlthmll)) in
  let val thl2 = erase_aconv_axiom (List.concat (map find_normthml atoml3)) in
  let val thl3 = erase_aconv_axiom (map simplify_thm thl2) in
    (atoml4,erase_aconv_axiom (thl1 @ thl3))
  end end end end end 
  end end end end end

fun mk_bcooperthml_proof_goal proof goal =
  let val axioml = [integerTheory.INT_ADD_COMM, integerTheory.INT_ADD_ASSOC]
  in
  let val (atoml,thml) = get_atomlthml_proof_goal proof goal in
    axioml @ thml @ (mk_bcooperthml_atoml atoml)
  end end

fun METIS_COOPER_BEAGLE_TAC proof goal =
  let val cooperthml = mk_bcooperthml_proof_goal proof goal in
    (
    (list_ASSUME_TAC cooperthml) THEN
    (metisTools.FO_METIS_TAC [])
    ) 
    goal
  end
(* test

*)


 end