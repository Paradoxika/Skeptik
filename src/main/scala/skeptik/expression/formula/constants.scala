package skeptik.expression

import skeptik.expression._
import skeptik.util.unicode._

package object formula {
  val andS = unicodeOrElse("\u2227","&")
  def andC = Var(andS, o -> (o -> o))
  
  val orS = unicodeOrElse("\u2228","&")
  def orC = Var(orS, o -> (o -> o))
  
  val impS = unicodeOrElse("\u2192","->")
  def impC = Var(impS, o -> (o -> o))

  val allS = unicodeOrElse("\u2200","A")
  def allC(t:T) = Var(allS, (t -> o ) -> o)
  
  val exS = unicodeOrElse("\u2203","E")
  def exC(t:T) = Var(exS, (t -> o ) -> o)
  
  val negS = unicodeOrElse("\u00AC","-")
  def negC = Var(negS, o -> o)
  
  def isLogicalConnective(c:E) = c match {
    case c: Var => {
      val n = c.name 
      if (n == andS || n == impS || n == allS || n == exS || n == negS) true else false
    }
    case _ => false
  }
}