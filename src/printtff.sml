structure printtff :> printtff =
struct

open HolKernel HOLPP numSyntax higherorder namevar extractvar nametype extracttype 
stringtools listtools mydatatype (*not all structures are necessary*)

fun PRINTTFF_ERR function message =
    HOL_ERR{origin_structure = "printtff",
            origin_function = function,
            message = message}


val bvcounter = ref 0 (* warning: use of a global reference *)
(*PRINTTERM*)

(* add some properties for numeral *) (* does two things at once *)
fun numl l =
  case l of
    [] => []
  | v :: m => (
              case typecat (type_of v) of
                Numtype => mk_geq (v,``0``) :: numl m
              | _ => numl m 
              )

fun addnumprop l term = 
  case (numl l) of
    [] => term
  | _ => mk_conj (list_mk_conj (numl l),term) 
(* end *)
 

(* name a list of bv and push it over the stack *)
(* warning: modify bvcounter *)
fun addbvltobvnm bvl bvnm = 
  case bvl of
    [] => bvnm
  | bv :: m => (
               bvcounter := (!bvcounter) + 1;
               (bv,namebvn bv ((!bvcounter) - 1)) :: (addbvltobvnm m bvnm) 
               )
 
fun printbvl2 pps bvl bvnm tynm  =
  case bvl of
    [] => raise PRINTTFF_ERR "printbvl2" "emptylist"
  | [bv] => ( (* the bound variables should have a simple type *)
            add_string pps (lookup bv bvnm); 
            add_string pps ": ";
            add_string pps (lookup (type_of bv,0) tynm)
            ) 
  | bv :: m => (
               add_string pps (lookup bv bvnm); 
               add_string pps ": ";
               add_string pps (lookup (type_of bv,0) tynm); 
               add_string pps ","; 
               printbvl2 pps m bvnm tynm
               )  

fun printbvl pps bvl bvnm tynm = 
  (
  add_string pps "[";
  printbvl2 pps bvl bvnm tynm;
  add_string pps "]"
  )

(* #1 state : list of (free variable or undefined constant, its name) *)
(* #2 state : list of (bound variable, its name)  *)
(* #3 state : list of (alphatype, its name) *)
(* modify bvcounter *)

fun printterm pps term state =
  case termstructure term of
    Numeral => add_string pps (namenumeral term)
  | Var => if ismember term (fstcomponent (#2 state))
           then add_string pps (lookup term (#2 state)) (*boundvar*)
           else add_string pps (lookup term (#1 state)) (*freevar*)
  | Const => (
             case leafconst term of
               True => add_string pps "$true"
             | False => add_string pps "$false"
             | Newleafconst => add_string pps (lookup term (#1 state))
             )
  | Comb => (
            case connective term of
              Conj => binop pps "&" term state
            | Disj => binop pps "|" term state
            | Neg => unop pps "~" term state 
            | Imp_only => binop pps "=>" term state 
            | Forall => let val (qbvl,t) = strip_forall term in
                          quantifier pps "!" qbvl t state
                        end       
            | Exists => let val (qbvl,t) = strip_exists term in
                          quantifier pps "?" qbvl t state
                        end
            | App => let val (operator,argl) = strip_comb term in
                       case termstructure operator of
                         Numeral => raise PRINTTFF_ERR "printterm" "operator is numeral"
                       | Var => application pps (lookup operator (#1 state)) argl state  (* don't need to test if it's bound because operator can't be bound *)
                       | Const => (
                                  case nodeconst term of
                                    Eq => binop pps "=" term state
                                  | Add => application pps "$sum" argl state
                                  | Minus => application pps "$difference" argl state  
                                  | Mult => application pps "$product" argl state  
                                  | Less => application pps "$less" argl state  
                                  | Greater => application pps "$greater" argl state  
                                  | Geq => application pps "$greatereq" argl state  
                                  | Leq => application pps "$lesseq" argl state
                                  | Newnodeconst => application pps (lookup operator (#1 state)) argl state      
                                  )
                       | Comb => raise PRINTTFF_ERR "printterm" "operator is comb"
                       | Abs => raise PRINTTFF_ERR "printterm" "abstraction"
                     end
             )
  | Abs => raise PRINTTFF_ERR "printterm" "abstraction"

and printterml pps terml state = 
  case terml of
    [] => raise PRINTTFF_ERR "printterml" "emptylist"
  | [t] => printterm pps t state
  | t :: m => ( 
              printterm pps t state; 
              add_string pps ",";
              printterml pps m state
              ) 
and unop pps str term state =
  let val (operator,l) = strip_comb term in
  let val lhs =  hd l in
    (
    add_string pps ("( " ^ str ^ " ");
    printterm pps lhs state;
    add_string pps " )"
    )
  end end
and binop pps str term state = 
  let val (operator,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in   
    (
    add_string pps "( ";
    printterm pps lhs state;
    add_string pps (" " ^ str ^ " ");
    printterm pps rhs state;
    add_string pps " )"
    )
  end end
and quantifier pps str bvl term state = (* to do add num axiom for bound variable *)
  let val newbvnm = addbvltobvnm bvl (#2 state) in
  let val newterm = addnumprop bvl term in
  ( 
      add_string pps (str ^ " ");
      printbvl pps bvl newbvnm (#3 state);
      add_string pps " : ";  
        
      add_string pps "( "; 
      printterm pps newterm (#1 state,newbvnm,#3 state);
      add_string pps " )" 
    )
  end end
and application pps str argl state =
  (
  add_string pps str;
  add_string pps "(";
  printterml pps argl state; 
  add_string pps ")"
  )
(* END PRINTTERM *)


(* PRINTTHM *)

(* useful functions *)
fun nl2 pps = (
                add_newline pps;
                add_newline pps
                ) 
fun indent4 pps = ((* to be replaced with begin block maybe *)
                    add_newline pps; 
                    add_string pps (space 4)
)

(* could be in extracttype *)
fun erasedefinedtype leafvty_nm = 
  case leafvty_nm of
    [] => []
  | (leafvty,nm) :: m => 
    (
    case typecat (fst leafvty) of
      Booltype => erasedefinedtype m
    | Numtype => erasedefinedtype m
    | _ => (leafvty,nm) :: erasedefinedtype m
    )

fun printtype pps str tystr =
  ( 
  add_string pps ("tff(" ^ str ^ "_type,type,(");
  indent4 pps;
  add_string pps (str ^ ": " ^ tystr ^ " )).")
  ) 

(* should only print leafvty *)
fun printtypel pps tydict =
   case tydict of
    [] => ()
  | (ty,nm) :: m => (
                    printtype pps nm "$tType";
                    nl2 pps;
                    printtypel pps m
                    )         

(* free variables or undefined constant *)
fun printfvcl pps fvc_narg_nm tydict =
  case fvc_narg_nm of
    [] => () 
  | (fvc,narg,nm) :: m => (
                          printtype pps nm (lookup (type_of fvc,narg) tydict);
                          nl2 pps;
                          printfvcl pps m tydict
                          )

(* axiom *)
  (* tools *)
fun nameaxioml2 axioml start = 
  case axioml of
    [] => []
  | a :: m => (a,namestrn "axiom" start) :: nameaxioml2 m (start + 1)
 
fun nameaxioml axioml = nameaxioml2 axioml 0
  
fun printaxiom pps name prop state = 
  (
  add_string pps ("tff(" ^ name ^ "_axiom,axiom,(");
  indent4 pps;
  printterm pps prop state;
  add_string pps " ))." 
  )
  (* numaxiom *)
fun printnumaxiom pps state =
  let val fvcl = fstcomponent (#1 state) in
  let val l = numl fvcl in
  
    if isempty l then ()
    else let val prop = list_mk_conj l in
         (
         printaxiom pps "numeral" prop state;
         nl2 pps
         )
         end
  end end
  (* axiomlist *)
fun printaxioml pps axiomnm state =
  case axiomnm of
    [] => ()
  | (axiom,nm) :: m => (
                       printaxiom pps nm axiom state;
                       nl2 pps;
                       printaxioml pps m state
                       )

(* conjecture *)
fun printconjecture pps name prop state =
  (
  add_string pps ("tff(" ^ name ^ "_conjecture,conjecture,(");
  indent4 pps;
  printterm pps prop state;
  add_string pps " ))." 
  )

(* modify bvcounter *)
fun printthm pps thm =
  (
  bvcounter := 0
  ;
  let val goal = concl thm in
  let val hypl = hyp thm in 
  let val propl = hypl @ [concl thm] in
  (* variable extraction *)
  let val var_narg_cat = extractvarl propl in
  let val var_narg = erase3rdcomponent var_narg_cat in
  (* type extraction *)
  let val ty_narg = alltypel var_narg in
  let 
    val leafvtyl = leafvtypel ty_narg 
    val alphatyl = alphatypel ty_narg  
    val nodevtyl = nodevtypel ty_narg 
  in
  (* type name *)
  let val leafvty_nm = addleafvtypel leafvtyl [] in
  let val simplety_nm = addnodevsimpletypel nodevtyl leafvty_nm in
  let val tydict = addnodevtypel nodevtyl simplety_nm in 
  (* bound variable *)
  let val bv_narg = getbvnargl var_narg_cat in 
  (* free variable *)
  let val fvcdc_narg_cat = erasebv var_narg_cat in
  let val fvcdc_narg = erase3rdcomponent fvcdc_narg_cat in
  let val fvc_narg = getfvcnargl var_narg_cat in 
  let val fvc_narg_nm = namefvcl fvc_narg in
  let val fvc_nm = erase2ndcomponent fvc_narg_nm in
  (* axiom *)
  let val axiomnm = nameaxioml hypl in
  (* needed to call printterm *)
  let val state = (fvc_nm,[],tydict) in
    
  if firstorderbvl bv_narg
     andalso 
     firstorderfvcdcl fvcdc_narg
     andalso 
     not (booleanargl var_narg)
  then
    (
    begin_block pps CONSISTENT 0;
      printtypel pps (erasedefinedtype simplety_nm);
      printfvcl pps fvc_narg_nm tydict;
      printnumaxiom pps state;
      printaxioml pps axiomnm state;
      printconjecture pps "goal" goal state; 
    end_block pps
    )
  else
    raise PRINTTFF_ERR "printthm" "should not happen"

  end end end end end 
  end end end end end
  end end end end end
  end end end 
  (* Some day I'll get rich with all this ends *)
  ;
  bvcounter := 0
  )
(* END PRINTTHM *)

(* need the full path of your file (eg /home/problem.p) *)

fun outputtff path thm =
  let val file = TextIO.openOut path in 
  let val pps_tff = PP.mk_ppstream 
                      {
                      consumer  = fn s => TextIO.output (file,s),
                      linewidth = 79,
                      flush  = fn () => TextIO.flushOut file
                      } 
  in 
    (
    printthm pps_tff thm;
    TextIO.closeOut file
    )  
  end end
  

end



