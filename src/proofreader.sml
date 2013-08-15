structure proofreader :> proofreader =
struct

open HolKernel Abbrev boolLib normalForms numSyntax
     stringtools listtools tools mydatatype 
     extractvar freshvar extracttype namevar

fun PROOFREADER_ERR function message =
      HOL_ERR {origin_structure = "conv",
	             origin_function = function,
               message = message}
               
               
end