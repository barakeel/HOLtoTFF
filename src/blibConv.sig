signature blibConv =
sig

include Abbrev
 
  val rw_absbool : term -> term
  val APP_CONV : conv 
  val rw_app : term -> term
  val BOOL_BV_CONV : conv
  
end