structure printtff :> printtff =
struct

open HolKernel HOLPP numSyntax higherorder name extractvar extracttype stringtools listtools mydatatype  (*not all structures are necessary*)

fun PRINTTFF_ERR function message =
    HOL_ERR{origin_structure = "printtff",
            origin_function = function,
            message = message}

(*PRINTTERM*)
val bvcounter = ref 0; (* warning: use of a global reference *)

(* name a list of bv and push it over the stack *)
(* warning: modify bvcounter *)
fun addbvltobvnm bvl bvnm = 
  case bvl of
    [] => bvnm
  | bv :: m => (
               bvcounter := (!bvcounter) + 1;
               (bv,namebvn bv ((!bvcounter) - 1)) :: (addbvltobvnm m bvnm) 
               )
 
fun printbvl2 pps bvl bvnm alphanm  =
  case bvl of
    [] => raise PRINTTFF_ERR "printbvl2" "emptylist"
  | [bv] => ( (* the bound variables should have a simple type *)
            add_string pps (lookup bv bvnm);
            add_string pps ": ";
            add_string pps (namesimpletype (type_of bv) alphanm)
            ) 
  | bv :: m => (
               add_string pps (lookup bv bvnm); 
               add_string pps ": ";
               add_string pps (namesimpletype (type_of bv) alphanm); 
               add_string pps ","; 
               printbvl2 pps m bvnm alphanm
               )  

fun printbvl pps bvl bvnm alphanm = 
  (
  add_string pps "[";
  printbvl2 pps bvl bvnm alphanm;
  add_string pps "]"
  )

(* #1 state : list of (a free variable or an undefined constant c, its name) *)
(* #2 state : list of (bound variable, its name)  the type should defintly be a simple type *)
(* #3 state : list of (alphatype, its name) *)
(* warning: should have the same structure as getfvcl in extractterm.sml *)
(* modify bvcounter *)
(* pretty printing *)

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
                       | Var => application pps (lookup operator (#1 state)) argl state (* don't need to test if it's bound because operator can't be bound *)
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
and quantifier pps str bvl term state =
  let val newbvnm = addbvltobvnm bvl (#2 state) in
    ( 
    begin_block pps CONSISTENT 0;
      add_string pps (str ^ " ");
      printbvl pps bvl newbvnm (#3 state);
      add_string pps " : ";  
        add_string pps "( "; 
        printterm pps term (#1 state,newbvnm,#3 state);
        add_string pps " )"; 
    end_block pps 
    )
  end
and application pps str argl state =
  (
  add_string pps str;
  add_string pps "( ";
  printterml pps argl state; 
  add_string pps " )"
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

(* type *)
  (* preformat the type to be printed *)

fun bvsimpletypel bvl alphanm = 
  case bvl of
    [] => []
  | bv :: m => case typecat (type_of bv) of
                 Booltype => bvsimpletypel m alphanm
               | Numtype => bvsimpletypel m alphanm
               | _ =>  namesimpletype (type_of bv) alphanm :: bvsimpletypel m alphanm


fun fvcsimpletypel fvc_narg_nm_tynm =
  case fvc_narg_nm_tynm of
    [] => []
  | (fvc,0,nm,tynm) :: m => (
                              case typecat (type_of fvc) of
                                Booltype => fvcsimpletypel m  
                              | Numtype => fvcsimpletypel m  
                              | _ =>  tynm :: fvcsimpletypel m
                              )  
   | a :: m => fvcsimpletypel m 

fun simpletypel bvl fvc_narg_nm_typenm alphanm =
  erasedouble ((bvsimpletypel bvl alphanm) @ (fvcsimpletypel fvc_narg_nm_typenm))

 (* end of preformat *)

fun printtype pps nm tynm =
  ( 
  add_string pps ("tff(" ^ nm ^ "_type,type,(");
  indent4 pps;
  add_string pps (nm ^ ": " ^ tynm ^ " )).")
  ) 

fun printtypel pps simpletypel =
   case simpletypel of
    [] => ()
  | tynm :: m => (
                 printtype pps tynm "$tType";
                 nl2 pps;
                 printtypel pps m
                 )
              
(* free variables or undefined constant *)
fun printfvcl pps fvc_narg_nm_tynm =
  case fvc_narg_nm_tynm of
    [] => () 
  | (fvc,narg,nm,tynm) :: m => (
                                printtype pps nm tynm;
                                nl2 pps;
                                printfvcl pps m
                                )

(* axiom *)
  (* numaxiom *)
fun numl fvcnm = 
  case fvcnm of
    [] => []
  | (fvc,nm) :: m => 
                     (
                     case typecat (type_of fvc) of
                       Numtype => (fvc,nm) :: numl m 
                     | _ => numl m   
                     )

fun numaxiom pps fvcnmnum =
  case fvcnmnum of
    [] => ()   
  | [(fvc,nm)] => add_string pps ("$greatereq" ^ "(" ^ nm ^ ",0)")
  | (fvc,nm) :: m => (
                     add_string pps ("$greatereq" ^ "(" ^ nm ^ ",0)");
                     add_string pps " & ";
                     numaxiom pps m 
                     )

fun printnumaxiom pps fvcnm =
  let val fvcnmnum = numl fvcnm in
    case fvcnmnum of
      [] => ()  
    | _ => (
           add_string pps "tff(num_axiom,axiom,("; 
           indent4 pps;
           numaxiom pps fvcnmnum;
           add_string pps " ))."
           )   
  end
  (* end numaxiom *)
fun printaxiom pps name holprop state = 
  (
  add_string pps ("tff(" ^ name ^ "_axiom,axiom,(");
  indent4 pps;
  printterm pps holprop state;
  add_string pps " ))." 
  )

fun printaxioml pps axiomnm state =
  case axiomnm of
    [] => ()
  | (axiom,nm) :: m => (
                       printaxiom pps nm axiom state;
                       nl2 pps;
                       printaxioml pps m state
                       )
(* conjecture *)
fun printconjecture pps name holprop state =
  (
  add_string pps ("tff(" ^ name ^ "_conjecture,conjecture,(");
  indent4 pps;
  printterm pps holprop state;
  add_string pps " ))." 
  )

(* modify bvcounter *)
fun printthm pps thm =
  (
  bvcounter := 0
  ;
  let val hypl = hyp thm in 
  let val propl = hypl @ [concl thm] in
  (* variable extraction *)
  let val var_narg_cat = extractvarl propl in
  (* alphatype *)
  let val alphanm = namealphal var_narg_cat in  
  (* bound variable type *)
  let val bv_narg = getbvnargl var_narg_cat in 
  let val bvl = fstcomponent bv_narg in
  let val bvtyl = bvsimpletypel bvl in  
  (* free variable naming *)
  let val fvcdc_narg_cat = erasenumber (erasebv var_narg_cat) in
  let val fvcdc_narg = erase3rdcomponent fvcdc_narg_cat in
  let val fvc_narg = getfvcnargl var_narg_cat in 
  let val fvc_narg_nm = namefvcl fvc_narg in
  let val fvcnm = erase2ndcomponent fvc_narg_nm in
  let val fvc_narg_nm_tynm = addtypenm fvc_narg_nm alphanm in
  let val fvctyl = fvcsimpletypel fvc_narg_nm_tynm in 
  (* list of all the types to be printed *)
  let val simpletyl = simpletypel bvl fvc_narg_nm_tynm alphanm in
  (* axiom *)
  let val axiomnm = nameaxioml hypl in
  (* needed to call printterm *)
  let val state = (fvcnm,[],alphanm) in
    
  if firstorderbvl bv_narg
     andalso 
     firstorderfvcdcl fvcdc_narg
  then
    (
    begin_block pps CONSISTENT 0;
      printtypel pps simpletyl;
      printfvcl pps fvc_narg_nm_tynm;
      printnumaxiom pps fvcnm;
      printaxioml pps axiomnm state;
      printconjecture pps "goal" (concl thm) state;
    end_block pps
    )
  else
    raise PRINTTFF_ERR "printthm" "should not happen"

  end end end end end 
  end end end end end
  end end end end end
  end end
  ;
  bvcounter := 0
  )
(* END PRINTTHM *)

(* need the full path of your file (eg /home/problem.p) *)

fun outputtff path thm =
  let val file = TextIO.openOut path in 
  let val ppstff = PP.mk_ppstream 
                  {
                  consumer  = fn s => TextIO.output (file,s),
                  linewidth = 79,
                  flush  = fn () => TextIO.flushOut file
                  } 
  in
    (
    printthm ppstff thm;
    TextIO.closeOut file
    )  
  end end
  

end



