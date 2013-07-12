structure typetest:> typetest =
struct

open HolKernel

(* implication *)
val test_type1 =
  let val conclt = ``f (P ==> Q) = g 5`` in 
    mk_thm ([],conclt)
  end

end
