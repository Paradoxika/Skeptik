package at.logic.skeptik.expression
package object formula {
  import at.logic.skeptik.util.unicode._

  // Logical Symbols and Connectives
  
  val andS = unicodeOrElse("\u2227","&") // "∧"
  def andC = new Var(andS, o -> (o -> o)) with Infix
  
  val orS = unicodeOrElse("\u2228","|")
  def orC = new Var(orS, o -> (o -> o)) with Infix
  
  val impS = unicodeOrElse("\u2192","->")
  def impC = new Var(impS, o -> (o -> o)) with Infix

  val allS = unicodeOrElse("\u2200","A")
  def allC(t:T) = Var(allS, (t -> o ) -> o)
  
  val exS = unicodeOrElse("\u2203","E")
  def exC(t:T) = Var(exS, (t -> o ) -> o)
  
  val negS = unicodeOrElse("\u00AC","-")
  def negC = Var(negS, o -> o)
  
  def isLogicalConnective(c:E) = c match {
    case Var(n,_) if (n == andS || n == orS || n == impS || 
                      n == allS || n == exS || n == negS) => true
    case _ => false
  }
  
  
  implicit def enrichFormula(e: E) = new RichFormula(e)

  def neg(f: E) = Neg(f) 
  def ¬(f: E) = neg(f)
  
  def all(v:Var) = (f:E) => All(v,f)
  def ∀(v:Var) = all(v)
  
  def ex(v:Var) = (f:E) => Ex(v,f)
  def ∃(v:Var) = all(v)
}