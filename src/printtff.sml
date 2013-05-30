structure printtff :> printtff =
struct

open HolKernel numSyntax name extractterm extracttype stringtools listtools mydatatype (*not all structures are necessary*)

fun PRINTTFF_ERR function message =
    HOL_ERR{origin_structure = "printtff",
            origin_function = function,
            message = message}

(*PRINTTERM*)
val bvcounter = ref 0; (*warning: use of a global reference*)

(*modify bvcounter*)
fun addbvltobvnm bvl bvnm = 
  case bvl of
    [] => bvnm
  | bv :: m => (
               bvcounter := (!bvcounter) + 1;
               (bv,namebvn bv ((!bvcounter) - 1)) :: (addbvltobvnm m bvnm) 
               )
 
fun printbvl2 bvl bvnm alphanm  =
  case bvl of
    [] => raise PRINTTFF_ERR "printbvl2" "emptylist"
  | [a] => (map a bvnm) ^ ": " ^ (nametype (type_of a) alphanm)
  | a :: m => (map a bvnm) ^ ": " ^ (nametype (type_of a) alphanm) ^ 
              "," ^ (printbvl2 m bvnm alphanm)

fun printbvl bvl bvnm alphanm = "[" ^ (printbvl2 bvl bvnm alphanm) ^ "]"
  
(*#1 state : list of (a free variable or an undefined constant c, its name) *)
(*#2 state : list of (bound variable, its name) *)
(*#3 state : list of (alphatype, its name) *)
(*warning: should have the same structure as getfvcl in extractterm.sml*)
(*modify bvcounter*)
fun printterm term state =
  case termstructure term of
    Numeral => term_to_string term
  | Var => if ismember term (fstcomponent (#2 state))
           then map term (#2 state) (*boundvar*)
           else map term (#1 state) (*freevar*) 
  
  | Const => (
             case leafconst term of
               True => "$true"
             | False => "$false"
             | Newleafconst => map term (#1 state)
             )
  | Comb => (
            case connective term of
              Conj => tffbinop "&" term state
            | Disj => tffbinop "|" term state
            | Neg => tffunop "~" term state 
            | Imp_only => tffbinop "=>" term state 
            | Forall => let val (bvl,t) = strip_forall term in
                          quantifier "!" bvl t state 
                        end       
            | Exists => let val (bvl,t) = strip_exists term in
                          quantifier "?" bvl t state 
                        end
            | App => let val (operator,argl) = strip_comb term in
                     let val argstr =  "(" ^ (printterml argl state) ^ ")" in
                       case termstructure operator of
                         Numeral => raise PRINTTFF_ERR "printterm" "a numeral is not an operator"
                       | Var => (map operator (#1 state)) ^ argstr
                       | Const => (
                                  case nodeconst term of
                                    Eq => tffbinop "=" term state
                                  | Add => "$sum" ^ argstr
                                  | Minus => "$difference" ^ argstr
                                  | Mult => "$product" ^ argstr 
                                  | Less => "$less" ^ argstr
                                  | Greater => "$greater" ^ argstr
                                  | Geq => "$greatereq" ^ argstr 
                                  | Leq => "$lesseq" ^ argstr  
                                  | Newnodeconst => (map operator (#1 state)) ^ argstr      
                                  )
                       | Comb => raise PRINTTFF_ERR "printterm" "second order"
                       | Abs => raise PRINTTFF_ERR "printterm" "abstraction"
                     end end
             )
  | Abs => raise PRINTTFF_ERR "printterm" "abstraction"

and printterml list state = 
  case list of
    [] => raise PRINTTFF_ERR "printterml" "emptylist"
  | [t] => printterm t state
  | t :: m => (printterm t state) ^ "," ^ (printterml m state) 
and tffunop str term state =
  let val (operator,l) = strip_comb term in
  let val lhs =  hd l in
    "( " ^ str ^ " " ^ (printterm lhs state) ^ " )"
  end end
and tffbinop str term state = 
  let val (operator,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in   
    "( " ^ (printterm lhs state) ^ " " ^ str  ^ " " ^ (printterm rhs state) ^ " )"  
  end end
and quantifier str bvl term state =
  let val newbvnm = addbvltobvnm bvl (#2 state) in
    str ^ " " ^ (printbvl bvl newbvnm (#3 state)) ^ " : " ^   
    "( " ^ (printterm term (#1 state,newbvnm,#3 state)) ^ " )"
  end

fun printtermlocal term = 
  let val strresult = ref "" in
  (
  bvcounter := 0; 
  strresult := printterm term (namefvcl [term],[],namealphal [term]);
  bvcounter := 0;
  !strresult
  )
  end
(*END PRINTTERM*)

(*PRINTTHM*)
fun printtypestr name str =
 "tff(" ^ name ^ "_type,type,(" ^
 (indent 4) ^ name ^ ": " ^ str ^ " ))." 

fun printtype name holtype alphanm =
  printtypestr name (nametype holtype alphanm) 

(*alpha*) 
fun printalphatypel alphanm = 
  case alphanm of
    [] => ""
  | (alpha,name) :: m => (printtypestr name "$tType") ^ "\n\n" ^ printalphatypel m

(*simpletype*)
fun printsimpletypel simpletypel =   
  case simpletypel of
    [] => ""
  | a :: m => (printtypestr (nametype a []) "$tType") ^ "\n\n" ^ printsimpletypel m
              
(*free variables*)
fun printfvtypel fvcnm alphanm =
  case fvcnm of
    [] => "" 
  | (a,name) :: m => (printtype name (type_of a) alphanm) ^ "\n\n" ^ (printfvtypel m alphanm)

(*add an axiom "greater than 0" for numtype free variables*)
fun numl fvcnm = 
  case fvcnm of
    [] => []
  | (fvc,nm) :: m => (
                     case typecat (type_of fvc) of
                       Numtype => (fvc,nm) :: numl m 
                     | _ => numl m   
                     )

fun numaxiom fvcnmnum =
  case fvcnmnum of
    [] => ""   
  | [(fvc,nm)] => "$greatereq" ^ "(" ^ nm ^ ",0)"
  | (fvc,nm) :: m => "$greatereq" ^ "(" ^ nm ^ ",0)" ^ " & " ^ numaxiom m 

fun printnumaxiom2 fvcnmnum =
  case fvcnmnum of
    [] => ""
  | _ => "tff(num_axiom,axiom,(" ^ (indent 4) ^ (numaxiom fvcnmnum) ^ " ))." ^ "\n\n" 

fun printnumaxiom fvcnm = printnumaxiom2 (numl fvcnm)

(*axiom*)
fun printaxiom name holprop state =
  "tff(" ^ name ^ "_axiom,axiom,(" ^ (indent 4) ^
   (printterm holprop state) ^ " ))." 

fun printaxioml axiomnm fvcnm alphanm=
  case axiomnm of
    [] => ""
  | (a,name) :: m => (printaxiom name a (fvcnm,[],alphanm)) ^ "\n\n" 
                      ^ (printaxioml m fvcnm alphanm)

(*conjecture*)
fun printconjecture name holprop fvcnm alphanm=
  "tff(" ^ name ^ "_conjecture,conjecture,(" ^ 
  (indent 4) ^ (printterm holprop (fvcnm,[],alphanm)) ^ " ))." 

(*modify bvcounter*)
fun printthm thm =
  let val strresult = ref "" in
    (
    bvcounter := 0
    ;
    let val hypl = hyp thm in 
    let val propl = hypl @ [concl thm]  in
    let 
      val fvcnm = namefvcl propl 
      val simpletyl = simpletypel propl 
      val alphanm = namealphal propl 
      val axiomnm = nameaxioml hypl 
    in
      strresult :=
      (printalphatypel alphanm) ^ 
      (printsimpletypel simpletyl) ^
      (printfvtypel fvcnm alphanm) ^ 
      (printnumaxiom fvcnm) ^ 
      (printaxioml axiomnm fvcnm alphanm) ^
      (printconjecture "goal" (concl thm) fvcnm alphanm) 
    end end end
    ;
    bvcounter := 0
    ;
    !strresult
    )
  end
(*END PRINTTHM*)

(*need the full path of your file (eg /home/problem.p)*)
fun outputtff path thm =
  let val str = printthm thm in
  let val myfile = TextIO.openOut path in 
    ( 
    TextIO.output (myfile,str)
    ; 
    TextIO.closeOut myfile 
    )
  end end
  

end



