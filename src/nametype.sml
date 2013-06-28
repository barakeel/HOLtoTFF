structure nametype :> nametype =
struct

open HolKernel numSyntax 
     extract_var extracttype stringtools 
     listtools mydatatype namevar
         
fun NAMETYPE_ERR function message =
  HOL_ERR{origin_structure = "nametype",
          origin_function = function,
          message = message}

(* should add compound type like int list*)  
fun name_type ty = 
  case typecat ty of
    Booltype => fst (dest_type ty)
  | Numtype => fst (dest_type ty)
  | Alphatype => String.substring 
                 (dest_vartype ty,1,
                  String.size (dest_vartype ty) - 1 ) 
  | Leaftype => fst (dest_type ty)
  | Funtype => raise NAMETYPE_ERR "name_type" "funtype"
  | Prodtype => raise NAMETYPE_ERR "name_type" "prodtype"

fun name_tff_type ty = 
  let val name = name_type ty in 
    if is_alphanumor_ name
    then "ty_" ^ name
    else "ty_"
  end


fun name_simplety ty = 
  case typecat ty of
    Booltype => name_tff_type ty
  | Numtype => name_tff_type ty
  | Alphatype => name_tff_type ty
  | Leaftype => name_tff_type ty
  | Funtype => let val (str,l) = dest_type ty in
               let 
                 val ty1 = hd l
                 val ty2 = hd (tl l)
               in 
                 "p_" ^ (name_simplety ty1) ^ 
                 "_fun_" ^ (name_simplety ty2) ^ "_p" 
               end end  
  | Prodtype => let val (str,l) = dest_type ty in         
                let 
                  val ty1 = hd l
                  val ty2 = hd (tl l)
                in 
                  "p_" ^ (name_simplety ty1) ^ 
                  "_prod_" ^ (name_simplety ty2) ^ "_p"
                end end  

(* add add for a simpletype *) (* tyadict should already contain alphatydict *)
(* Booltype is an exception *) 
(* we should consider if he's found as an argument of a function *)
(* has to be found when extracting the variable *)
(* quantification over boolean is not good either *)


(* should add the axioms for boolean before if we encounter one boolean arg *)
(*
btrue : bool
bfalse : bool
/\ !x:bool x=xtrue or x=xfalse
*)


(* tyadict *)
fun add_simplety (ty,arity) tyadict =
  if arity <> 0 then
    raise NAMETYPE_ERR "add_simplety" "not a simpletype"
  else
    let val n = length tyadict in
      case typecat ty of
        Booltype => let val str = "$o" in
                      add_entry ((ty,0),str) tyadict
                    end 
      | Numtype => let val str = "$int" in
                     add_entry ((ty,0),str) tyadict
                   end
      | _ => let val str = name_new (name_simplety ty) tyadict in
               add_entry ((ty,0),str) tyadict
             end 
    end   

(* this function is done over and over *)
fun repeatchange change l changing = 
  case l of
    [] => changing
  | a :: m => repeatchange change m (change a changing)
   
fun add_simpletyl = repeatchange add_simplety 
  
(* on leafvtypel result *) 
fun add_leafvtyl tyal tyadict =  
  case tyal of
    [] => tyadict
  | (ty,0) :: m => addleafvtypel m (add_simplety (ty,0) tyadict)
  | _ => raise NAMETYPE_ERR "addleafvtype" "not a simpletype"


(* add other simpletype generated by a nodevar 
   i.e. : if f has type (int -> int -> bool, 1) then
   add (int,0) and (int -> bool,0)  *)
fun add_nodevsimplety (ty,arity) tyadict =
  let val (argl,image) = dest_type_nb (ty,arity) in
  let val tyal = image :: argl in 
    add_simpletyl tyal tyadict
  end end

(* on nodevtypel result *)
fun addnodevsimpletypel tyal tyadict =
  case tyal of
    [] => tyadict
 | (ty,arity) :: m => addnodevsimpletypel m (addnodevsimpletype (ty,arity) tyadict) 

(* when all the simple types are tyadict *)
fun nameargl tyal tyadict = 
  case tyal of
    [] => ""
  | [(ty,arity)] => lookup (ty,arity) tyadict  
  | (ty,arity) :: m => (lookup (ty,arity) tyadict) ^ " * " ^ (nameargl m tyadict)

fun name_compoundtype (argl,image) tyadict = 
  case argl of
    [] => lookup image tyadict
  | [(ty,arity)] => (lookup (ty,arity) tyadict) ^ " > " ^ (lookup image tyadict)
  | _ => "( " ^ (nameargl argl tyadict) ^ " )" ^ " > " ^ (lookup image tyadict)

(* add his own type *)
fun addnodevtype (ty,arity) tyadict =
   let val (argl,image) = dest_type_nb (ty,arity) in
   let val str = namecompoundtype (argl,image) tyadict in
     add_entry ((ty,arity),str) tyadict  
   end end

(* on nodevtypel result *) (* 3rd time doing the same kind of code (generalize or not) *)
fun addnodevtypel tyal tyadict =
  case tyal of
    [] => tyadict
  | (ty,arity) :: m => addnodevtypel m (addnodevtype (ty,arity) tyadict) 

(* not necessary *)

fun create_tyadict term =
  let val varacat = extract_var term in
    

(* should create a fvtyadict too *)
(* should create a bvtyadict too *)
(* should create a ctyadict too *)
(* should depend on the number of arguments *)

end
  
