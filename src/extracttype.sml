structure extracttype :> extracttype =
struct

open HolKernel listtools mydatatype extractvar

fun EXTRACTTYPE_ERR function message =
  HOL_ERR{origin_structure = "extracttype",
          origin_function = function,
          message = message}

(* on the result of extractvar *)
fun alltypel2 var_narg = 
  case var_narg of
    [] => []
  | (var,narg) :: m => (type_of var,narg) :: alltypel2 m

fun alltypel var_narg = erase_double (alltypel2 var_narg)

(* on the result of alltypel *)
fun alphatypel ty_narg = 
  case ty_narg of
    [] => []
  | (ty,0) :: m => (
                   case typecat ty of
                     Alphatype => (ty,0) :: alphatypel m 
                   | _ => alphatypel m
                   )
  | a :: m => alphatypel m

fun leafvtypel ty_narg =
  case ty_narg of
    [] => []
  | (ty,0) :: m => (ty,0) :: leafvtypel m
  | a :: m => leafvtypel m

fun nodevtypel ty_narg =
  case ty_narg of
    [] => []
  | (ty,0) :: m => nodevtypel m
  | (ty,narg) :: m => (ty,narg) :: nodevtypel m


(* recursive dest_type with a bound *)
fun desttypenb (ty,narg) = 
  case narg of
    0 => ([],(ty,0))
  | n => if n < 0 
         then raise EXTRACTTYPE_ERR "desttypenb" "negative number"
         else
           let val (str,list) = dest_type ty in 
           let 
             val ty1 = hd list
             val ty2 = hd (tl list) 
           in
           let val resl = desttypenb (ty2,(n-1)) in
           let
             val argl = fst resl
             val image = snd resl 
           in
             ((ty1,0) :: argl,image) 
           end end end end
        
 

end
