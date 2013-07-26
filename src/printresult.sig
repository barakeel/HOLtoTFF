signature printresult =
sig
  
  include Abbrev
  
  val ppres_thm : ppstream -> thm -> unit
  val ppres_term :  ppstream -> term -> unit
  val ppres_thml : ppstream -> thm list -> unit
  val ppres_terml : ppstream -> term list -> unit
  val ppres_goal : ppstream -> goal -> unit
  val ppres_problem : ppstream -> thm list -> goal -> unit
  val output_tffgoalpath : string -> string -> unit
  val ppres_smallresult : ppstream -> goal -> unit
  val output_smallresult : string -> goal -> string -> bool -> unit
  
end