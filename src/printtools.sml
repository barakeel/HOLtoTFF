structure printtools :> printtools =
struct

open HolKernel Abbrev boolLib numSyntax HOLPP
     stringtools listtools mydatatype


fun PRINTTOOLS_ERR function message =
    HOL_ERR{origin_structure = "tools",
	    origin_function = function,
            message = message}


fun open_file path appendflag =
  let val file = 
    if appendflag then TextIO.openAppend path else TextIO.openOut path
  in file end

fun outstream_eqth file name eqth =
  let val lt  = lhs (concl eqth) in
  let val rt = rhs (concl eqth) in
    if lt = rt then ()
    else
      (
      TextIO.output (file,name ^ ": ");
      TextIO.output (file,(term_to_string rt) ^ "\n") 
      )
  end end 


fun output_info path str = 
  let val file = TextIO.openAppend path in 
    (TextIO.output (file,str); TextIO.closeOut file) 
  end 

fun output_error path str =
  (
  output_info path str;
  PRINTTOOLS_ERR "output_error" str
  )




end