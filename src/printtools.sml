structure printtools :> printtools =
struct

open HolKernel Abbrev boolLib numSyntax HOLPP
     stringtools listtools mydatatype


fun PRINTTOOLS_ERR function message =
    HOL_ERR{origin_structure = "tools",
	    origin_function = function,
            message = message}

(* standard printing *)
fun output_info path str = 
  let val file = TextIO.openAppend path in 
    (TextIO.output (file,str); TextIO.closeOut file) 
  end 

fun output_error path str =
  (
  output_info path str;
  PRINTTOOLS_ERR "output_error" str
  )

(* pretty printing *)
fun pp_conv pps name eqth =
  let val lt  = lhs (concl eqth) in
  let val rt = rhs (concl eqth) in
    if lt = rt then ()
    else
    (add_string pps (name ^ ": ");
     add_string pps (term_to_string rt);
     add_newline pps)  
  end end 

fun pp_open path appendflag =
  let val file = 
    if appendflag then TextIO.openAppend path else TextIO.openOut path
  in 
  let val pps =   
    mk_ppstream
    {
    consumer  = fn s => TextIO.output (file,s),
    linewidth = 80,
    flush     = fn () => TextIO.flushOut file
    } 
  in
   (file,pps)
  end end


end