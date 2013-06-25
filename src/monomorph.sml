structure monomorph :> monomorph =
struct

(*
load "mydatatype"; open mydatatype;
load "listtools"; open listtools;
load "extractvar"; open extractvar;
 *)
open HolKernel numSyntax mydatatype listtools extractvar


type thm = Thm.thm
type term = Term.term
type fvcinfos =
  { term : Term.term, 
    def : thm option, 
    axiom : bool,
    replace : bool }

type hol_type = Type.hol_type
type subst = {redex: hol_type, residue: hol_type} list
type elsubst = {redex: hol_type, residue: hol_type}
type multisubst = {redex: hol_type, residuel: hol_type list} list
type elmultisubst = {redex: hol_type, residuel: hol_type list}

fun MONOMORPH_ERR function message =
    HOL_ERR{origin_structure = "monomorph",
            origin_function = function,
            message = message}


(* free variables or constant : instantiate f:alpha to f:type if f:type is in thm *)              
(* bound variables : instantiate b:alpha to any types in the formula *)
(* logical operator as $==> won't be instantiate 
   because it's already of type bool -> bool -> bool *)

(* return a theorem list *)
(* fun monomorph2_fvc fvc axiom conjecture =
  let val fvcl = get_fvcl conjecture in *)
  
fun name_of term = 
  case termstructure term of
    Numeral => Int.toString (numSyntax.int_of_term term)
  | Var => fst (dest_var term)
  | Const => fst (dest_const term)
  | Comb => raise MONOMORPH_ERR "name_of" "comb"
  | Abs => raise MONOMORPH_ERR "name_of" "abs"

(* extract a pre-substitution *)
fun make_presubst_2 fvc1 fvcl2 =
  case fvcl2 of
    [] => [] 
  | fvc2 :: m => 
    if name_of fvc1 = name_of fvc2
    then
      let val subst = match_type (type_of fvc1) (type_of fvc2) in
        subst @ (make_presubst_2 fvc1 m)
      end
      handle 
        _ => [] @ (make_presubst_2 fvc1 m)
    else 
      make_presubst_2 fvc1 m

fun make_presubst fvc1 fvcl2 = erase_double (make_presubst_2 fvc1 fvcl2) 

fun make_presubst_l_2 fvcl1 fvcl2 =
  case fvcl1 of  
    [] => []
  | fvc1 :: m => make_presubst fvc1 fvcl2 @ make_presubst_l_2 m fvcl2

fun make_presubst_l fvcl1 fvcl2 = erase_double (make_presubst_l_2 fvcl1 fvcl2)

fun extract_presubst thm1 thm2 =
  let 
    val fvcl1 = get_fvcl_thm thm1
    val fvcl2 = get_fvcl_thm thm2
  in
    make_presubst_l fvcl1 fvcl2
  end
(* end *)

(* create a multisubst out of it *)
fun is_redex_in redex (multisubst: multisubst) =
  case multisubst of
    [] => false
  | a :: m => 
    if redex = #redex a
    then true
    else is_redex_in redex m
  
fun get_residuel redex (multisubst: multisubst) =
   case multisubst of
    [] => raise MONOMORPH_ERR "get_residuel" "redex not found"
  | a :: m => 
    if redex = #redex a
    then #residuel a
    else get_residuel redex m

fun replace (elmultisubst: elmultisubst) (multisubst: multisubst) =            
  case multisubst of
    [] => []
  | a :: m => if #redex elmultisubst = #redex a
              then elmultisubst :: m
              else a :: replace elmultisubst m 
              
fun regroup_el (elsubst: elsubst) (multisubst: multisubst) =
  let 
    val redex = #redex elsubst
    val residue = #residue elsubst
  in
    if is_redex_in redex multisubst
    then
      let val residuel = get_residuel redex multisubst in
      let val newresiduel = add_once residue residuel in
        replace {redex = redex, residuel = newresiduel} multisubst
      end end
    else  
       {redex = redex, residuel = [residue]} :: multisubst 
  end    
  
fun regroup2 (subst:subst) multisubst =
  case subst of
    [] => multisubst
  | elsubst :: m => regroup2 m (regroup_el elsubst multisubst)
   
fun regroup subst = regroup2 subst []
(* end *)

(* convert to a list of substitution *)
fun expand_subst (elmultisubst: elmultisubst) (subst: subst) =
  let 
    val redex = #redex elmultisubst
    val resl = #residuel elmultisubst 
  in
    case resl of
      [] => raise MONOMORPH_ERR "expand_subst" "empty list"
    | [ty] => [add_once {redex = redex, residue = ty} subst]
    | ty :: m => add_once {redex = redex, residue = ty} subst :: 
                 expand_subst {redex = redex, residuel = m} subst
  end

  (* returns a list of substitution *)
fun expandl_subst multisubst subst =
  case multisubst of
    [] => [subst]
  | multi :: m => expand_subst multi subst @ expandl_subst m subst

  (* returns a list of substitution *)   
fun expandel (elmultisubst: elmultisubst) (substl: subst list) =
  case substl of
    [] => expand_subst elmultisubst []
  | subst :: m => expand_subst elmultisubst subst @
                  expandel elmultisubst m
  
  (* returns a list of substitution *) 
fun expandl (multisubst: multisubst) (substl: subst list)  =
  case multisubst of
    [] => substl
  | elmultisubst :: m => expandl m (expandel elmultisubst substl)


fun expand (multisubst: multisubst) = expandl (multisubst: multisubst) []
(* end *)

(* summary function *)
fun extract_fvcsubstl thm1 thm2 = 
  let val presubst = extract_presubst thm1 thm2 in
  let val multisubst = regroup presubst in
    expand multisubst 
  end end


fun inst_type_l substl thm =
  case substl of
    [] => []
  | subst :: m => INST_TYPE subst thm :: inst_type_l m thm
(* if the empty subst occurs it's applied but it shouldn't *)

fun monomorph_fvc thm1 thm2 =
  let val substl = extract_fvcsubstl thm1 thm2 in
    inst_type_l substl thm1
  end

fun monomorph_fvc_l thml1 thm2  =
  case thml1 of 
    [] => []
  | thm1 :: m => monomorph_fvc thm1 thm2 @ monomorph_fvc_l m thm2

fun monomorph_fvc_l_l thml1 thml2 =
  case thml2 of
    [] => []
  | thm2 :: m => monomorph_fvc_l thml1 thm2 @ monomorph_fvc_l_l thml1 m

[|- $?! = (λP. $? P ∧ ∀x y. P x ∧ P y ⇒ (x = y))]
(* test   
val thm1 = ASSUME ``x:num = x`` ;
val thm2 = ASSUME ``?!x. x = 0``;
val thm3 = SELECT_AX;
val thm4 = EXISTS_UNIQUE_DEF;
val substl = extract_fvcsubstl thm4 thm2;
val axioml = inst_type_l substl thm4;
val axiomlres = monomorph_fvc axiom conjecture;  
val mo = monomorph_fvc_l_l [thm4] [thm1,thm2];
val a = monomorph_fvc_l [thm4] thm1; 
 *)  
end

           