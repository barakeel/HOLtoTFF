structure monomorph :> monomorph =
struct

(* testing *) 
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
fun monomorph2_fvc fvc axiom conjecture =
  let val fvcl = get_fvcl conjecture in
  
fun name_of term = 
  case termstructure term of
    Numeral => Int.toString (numSyntax.int_of_term term)
  | Var => fst (dest_var term)
  | Const => fst (dest_const term)
  | Comb => raise MONOMORPH_ERR "name_of" "comb"
  | Abs => raise MONOMORPH_ERR "name_of" "abs"

(* extract a substitution from an axiom and a conjecture *)
fun make_subst_2 fvc fvcl =
  case fvcl of
    [] => [] 
  | fvc2 :: m => 
    if name_of fvc = name_of fvc2
    then
      let val subst = match_type (type_of fvc) (type_of fvc2) in
        subst @ (make_subst_2 fvc m)
      end
      handle 
        _ => [] @ (make_subst_2 fvc m)
    else 
      make_subst_2 fvc m

fun make_subst fvc fvcl = erase_double (make_subst_2 fvc fvcl) 

fun make_subst_l_2 fvcl2 fvcl =
  case fvcl2 of  
    [] => []
  | fvc2 :: m => make_subst fvc2 fvcl @ make_subst_l_2 m fvcl

fun make_subst_l fvcl2 fvcl = erase_double (make_subst_l_2 fvcl2 fvcl)

fun extract_subst axiom conjecture =
 


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
fun expand (elmultisubst: elmultisubst) (substl: subst list) =
  case substl of
    [] => substl
  | subst :: m => expand_subst elmultisubst subst @
                  expand elmultisubst m
  
(* returns a list of substitution *) 
fun expandl2 (multisubst: multisubst) (substl: subst list)  =
  case multisubst of
    [] => substl
  | elmultisubst :: m => expandl2 m (expand elmultisubst substl)

fun expandl (multisubst: multisubst) = expandl2 (multisubst: multisubst) []

(* summary function*)
fun get_allsubst = 


match_type ``:bool`` ``:num``;

       match_type
       
INST_TYPE [(``:'a`` |-> ``:bool``)] 
          (ASSUME ``(f:'a->bool) (x:'a)``);
  concl it;
  type_of (fst(dest_comb it)); 
(* pattern matching against the structure is better *)
fun monomorph_fvc axiom conjecturety conjecture  =
  let val axiomfvcl = get_fvcl axiom in  
    case axiomfvcl of
  

fun monomorph_ 
           