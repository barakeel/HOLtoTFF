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
val theoryl = [ 
"alist", "arithmetic", "ASCIInumbers", "bag", "basicSize",
"basis_emit", "bitstring", "bit", "blast",
"bool","canonical","Coder","combin","complex",
"ConseqConv","container","Decode","DeepSyntax","defCNF", 
"divides","Encode","EncodeVar","enumeral","extended_emit",
"extreal","fcp","finite_map","fixedPoint","float","fmapal",
"fmaptree","frac","gcdset","gcd","HolSmt","hrat","hreal",
"ieee","ind_type","inftree","int_arith","integer_word",
"integerRing","integer","integral","intExtension","intreal",
"intto","lbtree","lebesgue","lim","list","llist","logroot",
"marker","measure","nets","normalForms","numeral_bit","numeral",
"numpair","numposrep","numRing","num","Omega_Automata","Omega",
"one","operator","option","pair","Past_Temporal_Logic","path",
"patricia_casts","patricia","poly","poset","powser","pred_set",
"prelim","prim_rec","primeFactor","probability","quantHeuristics",
"quote","quotient_list","quotient_option","quotient_pair",
"quotient_pred_set","quotient_sum","quotient","ratRing","rat",
"real_sigma","realax","real","relation","res_quan","rich_list",
"ringNorm","ring","sat","semi_ring","seq","set_relation","sorting",
"state_option","state_transformer","string_num","string","sum_num",
"sum","tc","Temporal_Logic","topology",
"toto","transc","update","util_prob","while","words","wot"   
];
fun add_theory theory = theory ^ "Theory";
app (load o add_theory) theoryl;

load "blibExtract"; open blibExtract;
fun is_arith_thm thm = null (get_cl_thm thm);
val thml = map (fst o snd) (DB.matchp is_arith_thm ["int_arith","integer"]);

beagle_nf ([],dest_thm integerTheory.INT_LE_SUB_LADD);
BEAGLE_TAC [] (dest_thm integerTheory.INT_LE_SUB_LADD);

load "blibTools"; open blibTools;
val badthml = filter (not o (success (BEAGLE_TAC []))) (map dest_thm thml);

BEAGLE_TAC [] ([],``0 = -10``);
beagle_nf ([] ,([],``0 = -10``));
is_int_literal ``0``;