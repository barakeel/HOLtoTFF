structure basicconv :> basicconv =
struct

open HolKernel Abbrev boolLib numSyntax
     basictools stringtools listtools

fun BASICCONV_ERR function message =
    HOL_ERR {origin_structure = "basicconv",
	           origin_function = function,
             message = message}

fun repeat_n_conv n conv = 
  case n of
    0 => ALL_CONV
  | n => if n < 0 then raise BASICCONV_ERR "repeat_n_conv" ""  
         else
           conv THENC repeat_n_conv (n - 1) conv

fun not_strip_exists_conv term =
  let val n = length (fst (strip_exists (dest_neg term))) in
    repeat_n_conv n (STRIP_QUANT_CONV NOT_EXISTS_CONV) term
  end  

fun strip_forall_not_conv term = 
  if is_forall term 
  then ((LAST_FORALL_CONV FORALL_NOT_CONV) THENC strip_forall_not_conv) term
  else raise UNCHANGED
  
  
end