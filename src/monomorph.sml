structure monomorph :> monomorph =
struct

open HolKernel Abbrev boolLib numSyntax 
     basictools listtools mydatatype
     syntax
     extractvar namevar

fun MONOMORPH_ERR function message =
    HOL_ERR{origin_structure = "monomorph",
            origin_function = function,
            message = message}


(* TEST *)
fun is_polymorph term = (polymorphic o type_of) term
fun is_polymorph_thm thm = exists is_polymorph (get_cl_thm thm)
fun is_polymorph_pb (thml,goal) = exists is_polymorph_thm thml

(* SUBSTITION SET *)
fun get_redl subst =
  case subst of
    [] => [] 
  | {redex = red, residue = res} :: m => red :: get_redl m 
  
fun red_to_res red subst =
  case subst of
    [] => raise MONOMORPH_ERR "image_subst" "redex not found"  
  | {redex = red1, residue = res1} :: m => 
    if red = red1 then res1 else red_to_res red m
 
fun remove_red red subst =
  case subst of
    [] => []
  | {redex = red1, residue = res1} :: m => 
    if red = red1 
    then remove_red red m 
    else {redex = red1, residue = res1} :: remove_red red m 

fun same_res subst1 subst2 red  = 
  red_to_res red subst1 = red_to_res red subst2
   
fun compatible_subst subst1 subst2 =
  let val l1 = get_redl subst1 in
  let val l2 = get_redl subst2 in
  let val l3 = inter l1 l2 in
    all (same_res subst1 subst2) l3 
  end end end

fun merge_subst subst1 subst2 =
  let val l1 = get_redl subst1 in
  let val l2 = get_redl subst2 in
  let val l3 = inter l1 l2 in
  let val subst1aux = repeatchange remove_red l3 subst1 in
    subst1aux @ subst2
  end end end end  

(* SUBSTITUTION ARITHMETIC *)
fun add_subst subst1 subst2 =
  if compatible_subst subst1 subst2 
  then [merge_subst subst1 subst2]
  else [subst1,subst2]
  
fun multone_subst subst substl =
  case substl of
    [] => [[]]
  | s :: m => add_subst subst s @ multone_subst subst m
   
fun mult_subst substl1 substl2 =  
  case substl1 of
    [] => [[]]
  | s1 :: m => (multone_subst s1 substl2) @ (mult_subst m substl2)
  
fun list_mult_subst_aux substll =
  case substll of  
    [] => [[]]
  | s :: m =>  mult_subst (list_mult_subst_aux m) s
fun list_mult_subst l = list_mult_subst_aux (rev l)

(* SUBSTITUTION NORMALISATION *)
fun is_identity {redex = red, residue = res} = (red = res)
fun erase_identity subst = filter (not o is_identity) subst
fun less_ty (ty1,ty2) = (Type.compare (ty1,ty2) = LESS)
  
fun less_redres ({redex = r1, residue = _},{redex = r2, residue = _}) =
  less_ty (r1,r2)
    
fun normalize_subst subst =
  quicksort less_redres (erase_identity subst)
  
fun normalize_substl substl =
  erase_double (map normalize_subst substl)

(* MATCH *)
fun is_matchable c1 c2 =
  name_of c1 = name_of c2 andalso 
  success (match_type (type_of c1)) (type_of c2)
 
(* always add the identity to prevent multiplication by 0 *) 
fun match_c_to_cl const cl =
  case cl of
    [] => [[]]
  | c :: m => 
    if is_matchable const c
    then match_type (type_of const) (type_of c) :: 
         match_c_to_cl const m 
    else match_c_to_cl const m
 
(* remove = from monomorphisation *) 
fun is_equal c = (name_of c = "=") 

local fun is_interesting c =
  is_polymorph c andalso (not o is_equal) c
in
fun match_cl_to_cl cl1 cl2 = 
  normalize_substl (
  list_mult_subst ( 
     map (inv match_c_to_cl cl2) (filter is_interesting cl1)
  )) 
end

(* INSTANTIATION *) 
fun inst_c subst c = mk_const (name_of c,type_subst subst (type_of c))

fun inst_cl_aux substl cl = 
  case substl of 
    [] => []
  | s :: m => map (inst_c s) cl :: inst_cl_aux m cl

fun inst_cl substl cl = 
  wrap "monomorph" "inst_cl" "" list_merge (inst_cl_aux substl cl)

fun inst_cll substll clthml =
  if not (length substll = length clthml)
  then 
    raise MONOMORPH_ERR "inst_cll" "list of different length" 
  else
    case clthml of
        [] => []
      | _  => inst_cl (hd substll) (hd clthml) :: 
              inst_cll (tl substll) (tl clthml)

fun inst_thm substl thm  = 
  let val thml = map (inv INST_TYPE thm) substl in
    if null thml 
    then raise MONOMORPH_ERR "inst_thm" "empty subst list"
    else LIST_CONJ thml
  end

fun inst_thml substll thml =
  if not (length substll = length thml) 
  then 
    raise MONOMORPH_ERR "inst_thml" "list of different length" 
  else
    case thml of
        [] => []
      | _  => inst_thm (hd substll) (hd thml) :: 
              inst_thml (tl substll) (tl thml)

(* SUBSTITUTION CREATION *) 
fun create_substl clthm (clthml,clgoal) = 
  let val cl = erase_double (list_merge (clthml @ [clgoal]))
  in
    match_cl_to_cl clthm cl
  end

fun create_substll (clthml,clgoal) =
  map (inv create_substl (clthml,clgoal)) clthml

(* repeat till finding a fix point with arbitrary parameters*)
fun repeat_create_substll (clthml,clgoal) substll instnl =
  let val newsubstll = create_substll (clthml,clgoal) in
  let val newinstnl = map length newsubstll in
  let val idsubstll = make_list_n (length clthml) [] in
    if suml newinstnl <= suml instnl orelse
       suml newinstnl > 15
    then 
      if suml newinstnl < 45 then newsubstll else substll
    else 
      repeat_create_substll 
        (inst_cll newsubstll clthml,clgoal) newsubstll newinstnl
  end end end   
(* MONOMORPHISATION *)  
fun monomorph_pb_w (thml,goal) =
  let val clthml = map get_cl_thm thml in
  let val clgoal = get_cl_goal goal in
  let val substll = repeat_create_substll 
                     (clthml,clgoal) 
                     (make_list_n (length thml) [])
                     (make_list_n (length thml) 1)                     
  in
    (inst_thml substll thml,goal) 
  end end end
fun monomorph_pb pb = wrap "monomorph" "monomorph_pb" "" monomorph_pb_w pb

(* test   
 val th1 = ASSUME ``!x. x=x`` ;
 val th2 = ASSUME ``!y. y=y`` ;
 LIST_CONJ [th1,th2];
 
 show_assums := true;
val term = ``(z = y) /\ (x = 0)``;
val goal = ([term],F); 
val thm1 = mk_thm ([``(x = y)``],F); 
val thm2 = ASSUME ``x=0``;
val thml = [thm1,thm2];
*)

end

           