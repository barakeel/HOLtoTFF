structure numproblem :> numproblem =
struct

open HolKernel
   
(* *)
val pb_num1 = 
  let val conclt = ``(x = 1)  ==> (x + 1 = 2)`` in
  mk_thm ([],conclt)
  end


end
