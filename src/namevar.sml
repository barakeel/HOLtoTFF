structure namevar :> namevar =
struct

open HolKernel extract_var stringtools listtools mydatatype numSyntax

fun NAMEVAR_ERR function message =
  HOL_ERR{origin_structure = "namevar",
          origin_function = function,
          message = message}


(* numeral *)
fun namenumeral term =  
  case termstructure term of
    Numeral => holname term
  | _ => raise NAMEVAR_ERR "namenumeral" "not a numeral"

(* bv : bound variable *)
fun namebvn bv n = 
  if isalphanumor_ (holname bv) 
  then "X" ^ (Int.toString n)  ^ (holname bv)
  else "X" ^ (Int.toString n)

(* fvc : free variable or fvcant*)
fun namefvc2 startstr term =
  let val str = holname term in
     switch 
       [
       (islowerword str   ,str),
       (isalphanumor_ str , startstr ^ str),  
       (str = "," , "pair") 
       ]
       "holConst"
  end

fun namefvc term =  
  let val str = holname term in
    case termstructure term of
      Var => namefvc2 "x" term
    | Const => namefvc2 "c" term
    | _ => raise NAMEVAR_ERR "namefvc" "not a variable or a fvcant"
  end

(* try different name untill it finds one which is not already used
i.e. x,x0,x1,x2,... *) (* to improve this code make use of a dictionnary *)
fun namefvcl2 fvc_narg used = 
  case fvc_narg of
    [] => []
 | (fvc,narg) :: m => 
    let 
      val name = namefvc fvc
      val nameref = ref name
      val n = ref 0 
    in
      (
      while is_member (!nameref) used do 
        (
        nameref := name ^ (Int.toString (!n));
        n := (!n) + 1
        )
      ; 
      (fvc,narg,(!nameref)) :: namefvcl2 m ((!nameref) :: used)
      ) 
    end

fun namefvcl fvc_narg = namefvcl2 fvc_narg []


 
end
  
