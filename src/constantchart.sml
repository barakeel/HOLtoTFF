structure constantchart :> constantchart =
struct

open HolKernel stringtools

type thm = Thm.thm
type term = Term.term

type constinfos =
  { term : Term.term, 
    def : thm option, 
    axiom : bool,
    replace : bool }
    
fun CONSTANTCHART_ERR function message =
    HOL_ERR{origin_structure = "constantchart",
            origin_function = function,
            message = message}
         
fun mk_constchart (constl : term list) =
  case constl of
    [] => []
  | c :: m => { term = c ,
                def = (NONE : thm option),
                axiom = false,
                replace = false } 
              :: mk_constchart m


fun get_constinfos c (constchart : constinfos list) =
  case constchart of
    [] => raise CONSTANTCHART_ERR "get_constinfos" "notfound"
  | record :: m => 
        if c = #term record
        then
          record
        else
          get_constinfos c m
   
fun edit_constchart (record : constinfos) (constchart : constinfos list) =
  case constchart of
    [] => [record]
  | a :: m => if #term record = #term a
              then record :: m
              else a :: edit_constchart record m  

fun editl_constchart (recordl : constinfos list) (constchart : constinfos list) =
  case recordl of
    [] => constchart
  | a :: m => editl_constchart m (edit_constchart a constchart)
  
fun default_constchart = 
  let val initchart = mk_constchart (all_consts ()) in
    editl_constchart [
                     { term = ``$?!``, 
                        def = SOME of EXISTS_UNIQUE_DEF,
                        axiom = false, 
                        replace = true }
                     ]


 
