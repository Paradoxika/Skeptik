package skeptik.expression

import skeptik.expression._

package object formula {
  val andS = "&"
  def andC = Var(andS, o -> (o -> o))
  
  val impS = "->"
  def impC = Var(impS, o -> (o -> o))

  val allS = "A"
  def allC(t:T) = Var(allS, (t -> o ) -> o)
  
  val exS = "E"
  def exC(t:T) = Var(exS, (t -> o ) -> o)
  
  val negS = "-"
  def negC = Var(negS, o -> o)
  
  def isLogicalConnective(c:E) = c match {
    case c: Var => {
      val n = c.name 
      if (n == andS || n == impS || n == allS || n == exS || n == negS) true else false
    }
    case _ => false
  }
}