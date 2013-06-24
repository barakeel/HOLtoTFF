structure chart :> chart =
struct

open HolKernel 

type thm = Thm.thm
type term = Term.term
type fvcinfos =
  { term : Term.term, 
    def : thm option, 
    axiom : bool,
    replace : bool }
    
fun CHART_ERR function message =
    HOL_ERR{origin_structure = "chart",
            origin_function = function,
            message = message}
         
fun mk_fvcchart (fvcl : term list) axiomb replaceb =
  case fvcl of
    [] => []
  | fvc :: m => 
    { term = fvc ,
      def = (NONE : thm option),
      axiom = axiomb,
      replace = replaceb } 
    :: mk_fvcchart m


fun get_fvcinfos fvc (fvcchart: fvcinfos list) =
  case fvcchart of
    [] => raise CHART_ERR "get_fvcinfos" "notfound"
  | record :: m => 
    if fvc = #term record
    then record
    else get_fvcinfos fvc m

fun is_member fvc (fvcchart: fvcinfos list) =
   case fvcchart of
    [] => false
  | record :: m => 
    if fvc = #term record
    then true
    else is_member fvc m
  
   
fun edit_fvcchart (record: fvcinfos) (fvcchart: fvcinfos list) =
  case fvcchart of
    [] => [record]
  | a :: m => if #term record = #term a
              then record :: m
              else a :: edit_fvcchart record m  

fun editl_fvcchart (recordl: fvcinfos list) (fvcchart: fvcinfos list) =
  case recordl of
    [] => fvcchart
  | a :: m => editl_fvcchart m (edit_fvcchart a fvcchart)
  
  
(* hard-coded definition *)  
(* maybe should look into the file *)
fun default_constchart () = 
  let val initchart = mk_fvcchart (all_consts ()) false false in
    editl_fvcchart [
                   { term = ``$?!``, 
                     def = SOME EXISTS_UNIQUE_DEF,
                     axiom = false, 
                     replace = true}
                   ]
                   initchart

(* on extractvar result *)
fun get_fvcchart varcat =
  let val defaultconstchart = default_constchart () in
  let val fvcal = get_fvcal varcat in
  let val fvcl = fstcomponent(fstcomponent fvccat) in
  let val fvcchart = mk_fvcchart fvcl false false in
  

  end


 
