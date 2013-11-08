structure blibNametype :> blibNametype =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype 
     blibExtractvar blibFreshvar blibExtracttype 
   
fun NAMETYPE_ERR function message =
  HOL_ERR {origin_structure = "blibNametype",
           origin_function = function,
           message = message}


fun name_alphatype ty = 
  substring (dest_vartype ty, 1, size (dest_vartype ty) - 1) 

fun name_leaftype ty = 
  case structtype ty of
    Booltype => fst (dest_type ty)
  | Numtype => fst (dest_type ty)
  | Inttype => fst (dest_type ty)
  | Alphatype =>  name_alphatype ty
  | Leaftype => fst (dest_type ty)
  | _ => raise NAMETYPE_ERR "name_leaftype" "node type"

fun name_tfftype ty = 
  let val name = name_leaftype ty in 
    if is_alphanumor_ name
    then name
    else "unprintable"
  end

fun prename_simplety ty = 
  case structtype ty of
    Booltype => name_tfftype ty
  | Numtype => name_tfftype ty
  | Inttype => name_tfftype ty
  | Alphatype => name_tfftype ty
  | Leaftype => name_tfftype ty
  | Funtype => let val (str,l) = dest_type ty in
               let val ty1 = hd l in
               let val ty2 = hd (tl l) in 
                 (prename_simplety ty1) ^ "_F_" ^ (prename_simplety ty2) 
               end end end 
  | Prodtype => let val (str,l) = dest_type ty in         
                let val ty1 = hd l in
                let val ty2 = hd (tl l) in
                  (prename_simplety ty1) ^ "_P_" ^ (prename_simplety ty2)
                end end end 
  | Nodetype => let val (str,tyl) = dest_type ty in
                   if is_alphanumor_ str 
                   then str ^ "I" ^ (prename_simpletyl tyl) ^ "I"       
                   else "op" ^  "I" ^ (prename_simpletyl tyl) ^ "I"
                end
                                    
and prename_simpletyl tyl =
  case tyl of
    [] => ""
  | [ty] => prename_simplety ty
  | ty :: m => (prename_simplety ty) ^ "_" ^ (prename_simpletyl m)
  
fun name_simplety ty = 
  if String.size (prename_simplety ty) > 40
  then "toolong"
  else "ty_" ^ (prename_simplety ty)

(* CREATE THE TYPE ARITY DICTIONNARY *)
fun add_simpletya (ty,arity) tyadict =
  if arity <> 0 then
    raise NAMETYPE_ERR "add_simpletya" "not a simpletype"
  else
    let val n = length tyadict in
      case structtype ty of
        Booltype => let val str = "bool" in
                      add_entry ((ty,0),str) tyadict
                    end 
      | Numtype => let val str = "$int" in
                     erase_double (((ty,0),str) :: tyadict)
                   end
      | Inttype => let val str = "$int" in
                     erase_double (((ty,0),str) :: tyadict)
                   end
      | _ => let val str = name_simplety ty in
               add_newnamel [((ty,0),str)] tyadict
             end 
    end   

fun add_simpletyal keyl dict = repeat_change add_simpletya keyl dict

(* add other simple types generated by a compound type, i.e. : 
   if (int -> int -> bool, 1) is a type used 
   then add (int,0) and (int -> bool,0)  *)
fun add_innersimpletya (ty,arity) tyadict =
  let val (argl,image) = strip_type_n (ty,arity) in
  let val tyal = image :: argl in 
    add_simpletyal tyal tyadict
  end end
  
fun add_innersimpletyal keyl dict = repeat_change add_innersimpletya keyl dict

fun name_tyargl argl tyadict =
  case argl of
    [] => raise NAMETYPE_ERR "name_tyargl" "no arguments"
  | [(ty,arity)] => lookup (ty,arity) tyadict  
  | (ty,arity) :: m => (lookup (ty,arity) tyadict) ^ " * " ^
                       (name_tyargl m tyadict)
                       
fun name_compoundty (argl,image) tyadict = 
  case argl of
    [] => lookup image tyadict
  | [(ty,arity)] => (lookup (ty,arity) tyadict) ^ " > " ^
                    (lookup image tyadict)
  | _ => "( " ^ (name_tyargl argl tyadict) ^ " )" ^ " > " ^
         (lookup image tyadict)

(* add his own type *)
fun add_compoundtya (ty,arity) tyadict =
   let val (argl,image) = strip_type_n (ty,arity) in
   let val str = name_compoundty (argl,image) tyadict in
     add_entry ((ty,arity),str) tyadict  
   end end

fun add_compoundtyal keyl dict = repeat_change add_compoundtya keyl dict

fun create_tyadict term =
  let 
    val simpletyal = get_simpletyal term
    val compoundtyal = get_compoundtyal term 
  in
  let val simpletyadict = add_simpletyal simpletyal [] in
  let val newsimpletyadict = add_innersimpletyal compoundtyal simpletyadict in  
  let val tyadict = add_compoundtyal compoundtyal newsimpletyadict in
    tyadict
  end end end end 


end
  
