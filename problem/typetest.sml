structure typetest:> typetest =
struct

open HolKernel

(* implication *)
val test_type1 =
  let val goal = ``f (P ==> Q) = g 5`` in 
    mk_thm ([],goal)
  end

end
