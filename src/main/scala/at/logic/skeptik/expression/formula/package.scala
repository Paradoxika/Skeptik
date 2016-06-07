package at.logic.skeptik.expression
package object formula {
  import at.logic.skeptik.util.unicode._
  import language.implicitConversions

  // Logical Symbols and Connectives
  
  def booleanFunctionType(arity: Int): T = if (arity == 0) o 
                                           else (o -> booleanFunctionType(arity - 1)) 
  
  class BigConnective(symbol: String) {
    def apply(arity: Int) = if (arity == 2) new Var(symbol, booleanFunctionType(arity)) with Infix
                            else new Var(symbol, booleanFunctionType(arity))
  }                                         
                                           
  val andS = unicodeOrElse("\u2227","&") // "∧"
  val andC = new Var(andS, o -> (o -> o)) with Infix
  val bigAndC = new BigConnective(andS)
  
  val orS = unicodeOrElse("\u2228","|")
  val orC = new Var(orS, o -> (o -> o)) with Infix
  val bigOrC = new BigConnective(orS)
  
  val impS = unicodeOrElse("\u2192","->")
  val impC = new Var(impS, o -> (o -> o)) with Infix

  val allS = unicodeOrElse("\u2200","A")
  def allC(t:T) = Var(allS, (t -> o ) -> o)
  
  val exS = unicodeOrElse("\u2203","E")
  def exC(t:T) = Var(exS, (t -> o ) -> o)
  
  val negS = unicodeOrElse("\u00AC","-")
  val negC = Var(negS, o -> o)
  
  val eqS = "="
  def eqC(t:T) = new Var(eqS, (t -> (t -> o))) with Infix

  val equivS = "<=>"
  def equivC = new Var(equivS, (o -> (o -> o))) with Infix

  val conditionalConnectiveS = "conditionalFormula"
  val conditionalConnectiveC = new Var(conditionalConnectiveS,o->(o->(o->o)))

  def isLogicalConnective(c:E) = c match {
    case Var(n,_) =>  n == andS || n == orS || n == impS ||
                      n == allS || n == exS || n == negS ||
                      n == equivS || n == conditionalConnectiveS
    case _ => false
  }
  
  
  implicit def enrichFormula(e: E) = new RichFormula(e)

  // Since Scala accepts only !, ~, + and - as prefix unary operators,
  // the following methods cannot be implemented in RichFormula
  
  def neg(f: E) = Neg(f) 
  def ¬(f: E) = neg(f)
  
  def all(v:Var) = (f:E) => All(v,f)
  def ∀(v:Var) = all(v)
  
  def ex(v:Var) = (f:E) => Ex(v,f)
  def ∃(v:Var) = all(v)
  
  def bigOr(args: Iterable[E]) = AppRec(bigOrC(args.size), args)
  def bigAnd(args: Iterable[E]) = AppRec(bigAndC(args.size), args)
}