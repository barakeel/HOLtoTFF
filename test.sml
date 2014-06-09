(* LIBRARIES *)
(* 
load "blibTools"; open blibTools;
load "blibName"; open blibName;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;
load "blibPrinter"; open blibPrinter;
load "beagle"; open beagle;
load "intSyntax"; open intSyntax;
*)
(* some necessary extensionality theorems *)
val thm1 = INST_TYPE [alpha |-> ``:int``, beta |-> ``:int``] EQ_EXT;
val thm2 = INST_TYPE [alpha |-> bool, beta |-> bool] EQ_EXT;

val ALT_SIMPLIFY_CONV = SIMP_CONV (simpLib.++ (pureSimps.pure_ss, boolSimps.BOOL_ss)) [];
load "blibExtract"; open blibExtract;
fun is_arith_thm thm = null (get_cl_thm (CONV_RULE ALT_SIMPLIFY_CONV thm));

val thml =  map (fst o snd) (DB.matchp is_arith_thm ["bool"]);
load "blibTools"; open blibTools;
val badthml = filter (not o (success (BEAGLE_TAC [EQ_EXT,thm1,thm2]))) (map dest_thm thml);
List.length badthml;

val thm = dest_thm (List.nth (thml,12));
BEAGLE_TAC [EQ_EXT,thm1,thm2] thm;
(* add necessary theorems *)
(* instantiation of extensionality *)
success BEAGLE_TAC [thm2] (dest_thm (BOOL_FUN_CASES_THM));
val thml = List.nth (thml,13);
val (thml,goal) =  ([]:thm list,(dest_thm thm));
beagle_nf ([],(dest_thm thm));
beagle_nf ([], ([],));
(* test *)

beagle_nf ([], goal);



(* With dependencies *)
fun mk_assoc_thm thm = ((hd o fst o Tag.dep_of o Thm.tag) thm,thm)
fun has_dep thm = (not o null) ((snd o Tag.dep_of o Thm.tag) thm)
fun dep_name thm = (hd o fst o Tag.dep_of o Thm.tag) thm

val counter = ref 0

val thm = assoc "bool.112" sthml;;
val thml = map (C assoc sthml) ((snd o Tag.dep_of o Thm.tag) thm);
val goal = dest_thm thm;


fun BEAGLE_REPROVE sthml thm =
  let val thml = map (C assoc sthml) ((snd o Tag.dep_of o Thm.tag) thm) in 
    (TAC_PROOF (dest_thm thm, BEAGLE_TAC thml); counter := (!counter) + 1)
    handle _ => ()
  end
  
fun first_n n l = if n = 0 then [] else if n < 0 then raise ERR "" ""  
                  else if null l then [] 
                  else hd l :: first_n (n-1) (tl l)
                    
fun BEAGLE_REPROVE_THY str =
  let 
    val sthml = map (mk_assoc_thm o snd) (DB.thms str)
    val thml = filter has_dep (map snd sthml) 
  in
    (
    counter := 0;
    app 
    (fn x => (BEAGLE_REPROVE sthml x;print (Int.toString (!counter) ^ dep_name x))) 
    thml;
    (!counter, length thml) 
    )
  end
  
  BEAGLE_REPROVE_THY "bool";
  
 