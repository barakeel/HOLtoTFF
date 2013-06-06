structure name :> name =
struct

open HolKernel extractvar extracttype stringtools listtools mydatatype numSyntax

fun NAME_ERR function message =
  HOL_ERR{origin_structure = "name",
          origin_function = function,
          message = message}

(* HOLNAME *)
fun holnamety holtype = 
  case typecat holtype of
    Booltype => fst (dest_type holtype)
  | Numtype => fst (dest_type holtype)
  | Alphatype => raise NAME_ERR "holnamety" "alphatype"
  | Leaftype => fst (dest_type holtype)
  | Funtype => raise NAME_ERR "holnamety" "funtype"
  | Prodtype => raise NAME_ERR "holnamety" "prodtype"
  
fun holnamet term =
  case termstructure term of
    Numeral => Int.toString (int_of_term term)
  | Var => fst (dest_var term)
  | Const => fst (dest_const term)
  | Comb => raise NAME_ERR "holnamet" "comb"
  | Abs => raise NAME_ERR "holnamet" "abs"
(* END HOLNAME *)

(* NAMETYPE *)
(* name alphatype *)
fun namestrn str n = str ^ (Int.toString n) 

fun namealphal2 alphatyl start = 
  case alphatyl of
    [] => []
  | alpha :: m => (alpha,namestrn "alpha" start) :: namealphal2 m (start + 1) 
 
fun namealphal var_narg_cat = namealphal2 (alphatypel var_narg_cat) 0

 
(* namesimpletype *) (* clash may occurs at several points in this code*)
fun namesimpletype2 holtype alphanm = 
  case typecat holtype of
    Booltype => holnamety holtype
  | Numtype => holnamety holtype
  | Alphatype => lookup holtype alphanm (* clash could occur if your name your type alpha...num *)
  | Leaftype => let val str = holnamety holtype in
                    switchargerr str 
                      [
                      (islowerword   ,str),
                      (isalphanumor_ ,"ty_" ^ str)  (* all types should be alphanumor_ for now *)
                      ]
                      (NAME_ERR "namesimpletype2" "not alphanumor_")
                  end
  | Funtype => let val (str,list) = dest_type holtype in
               let val ty1 = hd list
                   val ty2 = hd (tl list)
               in 
                 "t_" ^ (namesimpletype2 ty1 alphanm) ^ "_to_" ^ (namesimpletype2 ty2 alphanm) ^ "_t" 
               end end  
  | Prodtype => let val (str,list) = dest_type holtype in         
                let val ty1 = hd list
                    val ty2 = hd (tl list)
                in 
                  "t_" ^ (namesimpletype2 ty1 alphanm) ^ "_p_" ^ (namesimpletype2 ty2 alphanm) ^ "_t"
                end end  

fun namesimpletype holtype alphanm = 
  case typecat holtype  of
    Booltype => "$o"
  | Numtype => "$int"
  | _ => namesimpletype2 holtype alphanm

fun namesimpletypel typel alphanm =
  case typel of
    [] => ""
  | [ty] => namesimpletype ty alphanm
  | ty :: m => (namesimpletype ty alphanm) ^ " * " ^ (namesimpletypel m alphanm)

fun namecompoundtype argl image alphanm = 
  case argl of
    [] => namesimpletype image alphanm
  | [ty] => (namesimpletype ty alphanm) ^ " > " ^ (namesimpletype image alphanm)
  | _ => "( " ^ (namesimpletypel argl alphanm) ^ " )" ^ " > " ^ (namesimpletype image alphanm)

fun desttypenb holtype nbarg = (* to be redefined to cope with prod type at least raise an exception *)
  case nbarg of
    0 => ([],holtype)
  | n => if n > 0 
         then 
           let val (str,list) = dest_type holtype in
           let 
             val ty1 = hd list
             val ty2 = hd (tl list) in
           let val resl = desttypenb ty2 (n-1) in
           let
             val argl = fst resl
             val image = snd resl in
           (ty1 :: argl,image) 
           end end end end
         else raise NAME_ERR "desttypenb" "negative number"

fun nametype holtype nbarg alphanm = 
  case typecat holtype of
    Booltype => namesimpletype holtype alphanm
  | Numtype => namesimpletype holtype alphanm
  | Alphatype => namesimpletype holtype alphanm
  | Leaftype => namesimpletype holtype alphanm
  | Funtype => let val (argl,image) = desttypenb holtype nbarg in (* strip_fun is bad *)
               namecompoundtype argl image alphanm
               end
  | Prodtype => namesimpletype holtype alphanm
(* END NAMETYPE *)

(* NAMEVAR *)
(* numeral *)
fun namenumeral term =  
  case termstructure term of
    Numeral => holnamet term
  | _ => raise NAME_ERR "namenumeral" "not a numeral"

(* bv : bound variable *)
fun namebvn bv n = 
  if isalphanumor_ (holnamet bv) 
  then "X" ^ (Int.toString n)  ^ (holnamet bv)
  else "X" ^ (Int.toString n)

(* fvc : free variable or constant*)
fun namefvc2 startstr term =
  let val str = holnamet term in
     switch 
       [
       (islowerword str   ,str),
       (isalphanumor_ str , startstr ^ str),  
       (str = "," , "pair") 
       ]
       "holConst"
  end

fun namefvc term =  
  let val str = holnamet term in
    case termstructure term of
      Var => namefvc2 "x" term
    | Const => namefvc2 "c" term
    | _ => raise NAME_ERR "namefvc" "not a variable or a constant"
  end

(* return a triplelist (fvc,nbarg,name) *)
fun namefvcl2 fvcl used = 
  case fvcl of
    [] => []
 | (fvc,nbarg) :: m => 
    let 
      val name = namefvc fvc
      val nameref = ref name
      val n = ref 0 
    in
    ( 
    while ismember (!nameref) used do 
    (
    nameref := name ^ (Int.toString (!n))  
    ;
    n := (!n) + 1
    )
    ; 
    (fvc,nbarg,(!nameref)) :: namefvcl2 m ((!nameref) :: used) 
    )
    end

fun namefvcl fvcl = namefvcl2 fvcl []

fun addtypenm fvcnml alphanm =
  case fvcnml of
    [] => []
  | (fv,nbarg,nm) :: m => (fv,nbarg,nm,nametype (type_of fv) nbarg alphanm) :: addtypenm m alphanm
  


(*END NAMEVAR*)
fun nameaxioml2 axioml start = 
  case axioml of
    [] => []
  | a :: m => (a,namestrn "axiom" start) :: nameaxioml2 m (start + 1)
 
fun nameaxioml axioml = nameaxioml2 axioml 0

 
end
  
