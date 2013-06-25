structure axiomordef :> axiomordef =
struct
(*
load "monomorph"; open monomorph;
load "extractvar"; open extractvar;
*)
open HolKernel monomorph

type thm = Thm.thm
type term = Term.term
type fvcinfos =
  { term: Term.term, 
    thm: thm option, 
    axiom: bool,
    def: bool }
    
fun AXIOMORDEF_ERR function message =
    HOL_ERR{origin_structure = "axiomordef",
            origin_function = function,
            message = message}
 
(* from user input *)
(* should add first default axioms 
   because default_def depends on default_axiom*) 
(* the monomorphism should be applied to any theorem here *)


(* DEFAULT SETTINGS *)         
(* tools *)
fun mk_fvcchart (fvcl: term list) (axiomb: bool) (defb: bool) =
  case fvcl of
    [] => []
  | fvc :: m => 
    { term = fvc ,
      thm = (NONE: thm option),
      axiom = axiomb,
      def = defb } 
    :: mk_fvcchart m axiomb defb


fun get_fvcinfos fvc (fvcchart: fvcinfos list) =
  case fvcchart of
    [] => raise AXIOMORDEF_ERR "get_fvcinfos" "notfound"
  | record :: m => 
    if name_of fvc = name_of (#term record)
    then record
    else get_fvcinfos fvc m

fun is_member fvc (fvcchart: fvcinfos list) =
   case fvcchart of
    [] => false
  | record :: m => 
    if name_of fvc = name_of (#term record)
    then true
    else is_member fvc m
  
   
fun edit_fvcchart (record: fvcinfos) (fvcchart: fvcinfos list) =
  case fvcchart of
    [] => [record]
  | a :: m => if name_of (#term record) = name_of (#term a)
              then record :: m
              else a :: edit_fvcchart record m  

fun editl_fvcchart (recordl: fvcinfos list) (fvcchart: fvcinfos list) =
  case recordl of
    [] => fvcchart
  | a :: m => editl_fvcchart m (edit_fvcchart a fvcchart)
(* end tools *)  
  
(* hard-coded definition *)  
(* maybe should look into the file *)
fun default_constchart () = 
  let val initchart = mk_fvcchart (all_consts ()) false false in
  let val edit1 =  editl_fvcchart [
                   { term = ``$?!``, 
                     thm = SOME EXISTS_UNIQUE_DEF,
                     axiom = false, 
                     def = true}
                   ]
                   initchart in
  let val edit2 =  editl_fvcchart [
                   { term = ``$@``, 
                     thm = SOME SELECT_AX,
                     axiom = true, 
                     def = false}
                   ]
                   edit1 in               
    edit2
  end end end
(* END *)  

(* INCLUDE DEFAULT AXIOMS AND DEF *)
(* don't need to care about the type right now *)
(* axiom *)
fun useful_axioml2 cl =
  let 
    val defaultconstchart = default_constchart ()
  in
    case cl of
      [] => []
    | c :: m => let val infos = get_fvcinfos c defaultconstchart in
                  if #axiom infos 
                  then #thm infos :: useful_axioml2 m
                  else useful_axioml2 m
                end
  end

fun useful_axioml thm =
  let val cl = get_cl_thm thm in
    useful_axioml2 cl
  end  

fun useful_axioml_l thml =
  case thml of
    [] => [] 
  | thm :: m => useful_axioml thm @ useful_axioml_l m
(* def *)  
 fun useful_defl2 cl =
  let 
    val defaultconstchart = default_constchart ()
  in
    case cl of
      [] => []
    | c :: m => let val infos = get_fvcinfos c defaultconstchart in
                  if #def infos 
                  then #thm infos :: useful_defl2 m
                  else useful_defl2 m
                end
  end

fun useful_defl thm =
  let val cl = get_cl_thm thm in
    useful_defl2 cl
  end  

fun useful_defl_l thml =
  case thml of
    [] => [] 
  | thm :: m => useful_defl thm @ useful_defl_l m 
  
  
  
(* should monomorph them before adding them *)
fun erase_option l =
  case l of
    [] => []
  | NONE :: m => erase_option m
  | SOME a :: m => a :: erase_option m  


fun monomorph_defaultaxioml thml =
  let val axioml = erase_option (useful_axioml_l thml) in
    monomorph_fvc_l_l defaultaxioml thml
  end
  
fun subst_defl_in thml =
  (* first it's compulsory to try to monomorph *)
  let val defl = erase_option (useful_defl_l thml) in
  let val monodefl = monomorph_fvc_l_l defl thml in
    map (SUBS monodefl) thml
  end end 




(* test   
default_constchart ();
val thm1 = ASSUME ``x:bool`` ;
val thm2 = ASSUME ``?!x. x = 0``;
get_fvcl_thm SELECT_AX;
val thml = [thm2,thm1];
val axioml = monomorph_defaultaxioml thml;
val defaultaxioml = erase_option (useful_axioml_l thml);
``$=`` should be treated specially
don't want to generate theorem because they match with equal
val res = subst_defl_in thml; 
*)


end


 
