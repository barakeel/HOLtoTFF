structure name :> name =
struct

open HolKernel extractterm extracttype stringtools listtools mydatatype

fun NAME_ERR function message =
  HOL_ERR{origin_structure = "name",
          origin_function = function,
          message = message}

(* NAMETYPE *)
fun namestrn str n = str ^ (Int.toString n) 

fun namealphal2 alphatypel start = 
  case alphatypel of
    [] => []
  | a :: m =>  (a,namestrn "alpha" start) :: namealphal2 m (start + 1) 
 
fun namealphal propl = namealphal2 (alphatypel propl) 0
 
(*convert an Funtype or Prodtype into a unique name when called*) 
(*type collison may happen*)
fun namesimpletype2 holtype alphanm = 
  case typecat holtype of
    Booltype => "bool"
  | Numtype => "num"
  | Alphatype => map holtype alphanm (*clash could occur if your name your type alpha...num*)
  | Simpletype => let val str = erasechar (type_to_string holtype) in
                    switchargerr str 
                      [
                      (islowerword   ,str),
                      (isalphanumor_ ,"ty_" ^ str)  (*all types should be alphanumor_*)
                      ]
                      (NAME_ERR "namesimpletype2" "not alphanumor_")
                  end

(*shouldn't be apply to anything*)
  | Funtype => let val (str,list) = dest_type holtype in
               let val ty1 = hd list
                   val ty2 = hd (tl list)
               in 
                 "t_" ^ (namesimpletype2 ty1 alphanm) ^ "_to_" ^ (namesimpletype2 ty2 alphanm) ^ "_t" 
               end end  
(*everything that is under a product type is now unreachable*) 
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
  | [a] => namesimpletype a alphanm
  | a::m => (namesimpletype a alphanm) ^ " * " ^ (namesimpletypel m alphanm)
 
fun namecompoundtype typel holtype alphanm =
  case typel of
    [] => raise  NAME_ERR "namecompoundtype" ""
  | [a] => (namesimpletype a alphanm) ^ " > " ^ (namesimpletype holtype alphanm)
  | _ => "( " ^ (namesimpletypel typel alphanm) ^ " ) > " ^ (namesimpletype holtype alphanm) 

(*can now be replace by strip_fun*) 
(*fun striptype holtype =
  case typecat holtype of 
    Booltype => ([],holtype)
  | Numtype => ([],holtype)
  | Alphatype => ([],holtype)
  | Simpletype => ([],holtype)
  | Funtype => let val (str,list) = dest_type holtype in
               let val ty = hd list
                   val l = hd (tl list)
               in
                 (ty :: fst(striptype l), snd(striptype l)) 
               end end
  | Prodtype => ([], holtype) *)
 
fun nametype holtype alphanm = 
  case typecat holtype of
    Booltype => namesimpletype holtype alphanm
  | Numtype => namesimpletype holtype alphanm
  | Alphatype => namesimpletype holtype alphanm
  | Simpletype => namesimpletype holtype alphanm
  | Funtype => let val (a,b) = strip_fun holtype in
               namecompoundtype a b alphanm
               end
  | Prodtype => namesimpletype holtype alphanm
(* END NAMETYPE *)

(* NAMETERM *)

(* bv : bound variable *)
fun namebvn bv n = 
  if isalphanumor_ (term_to_string bv) 
  then "X" ^ (Int.toString n)  ^ (term_to_string bv)
  else "X" ^ (Int.toString n)


(* fv : free variable *)
(* c : constant *)
(* fvc : free variable or constant*)
fun namefvc2 term =
  let val str = term_to_string term in
     switch 
       [
       (islowerword str   ,str),
       (isalphanumor_ str ,"x" ^ str),  (*all free variables should be alphanumor_*)
       (str = "$," , "pair") (*bad but can't help too hard to call is_pair here*)
       ]
       "holConst"
  end

fun namefvc term =  
  let val str = term_to_string term in
    case termstructure term of
      Var => namefvc2 term
    | Const => namefvc2 term
    | _ => raise NAME_ERR "namefvc" "not a variable or a constant"
  end

fun namefvcl2 fvclist used = 
  case fvclist of
    [] => []
  | a :: m => let 
                val name = namefvc a
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
                (a,(!nameref)) :: ( namefvcl2 m ((!nameref) :: used) )
                )
              end
 
fun namefvcl terml = namefvcl2 (getfvcl terml) []
(*END NAMETERM*)

fun nameaxioml2 axioml start = 
  case axioml of
    [] => []
  | a :: m => (a,namestrn "axiom" start) :: nameaxioml2 m (start + 1)
 
fun nameaxioml axioml = nameaxioml2 axioml 0

 
end
  
