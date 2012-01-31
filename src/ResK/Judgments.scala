package ResK

object judgments {
  import scala.collection.TraversableOnce
  import scala.collection.LinearSeq
  import ResK.expressions._
  import ResK.logicalConstants._
  
  abstract class Judgment
  class Sequent(val ant:List[E], val suc:List[E]) extends Judgment {
    def contains(f:E) = (ant contains f) || (suc contains f)
    def --(s:Sequent) = Sequent(ant -- s.ant, suc -- s.suc)
    def ++(s:Sequent) = Sequent(ant ++ s.ant, suc ++ s.suc)
    def +(f:E) = new Sequent(ant, f::suc)
    def +:(f:E) = new Sequent(f::ant, suc)
    def -(f:E) = new Sequent(ant, suc - f)
    def -:(f:E) = new Sequent(ant - f, suc)    
    
    def ==(s:Sequent) = (ant.toSet == s.ant.toSet) || (suc.toSet == s.suc.toSet)
    override def hashCode = 42*ant.toSet.hashCode + suc.toSet.hashCode
    private def cedentToString(l:List[E]) = l match {
      case Nil => ""
      case h::t => (h.toString /: t)((x,y) => x + ", " + y)
    }
    override def toString = cedentToString(ant) + " :- " + cedentToString(suc)
  }
  object Sequent {
    def apply(ant:List[E], suc:List[E]) = new Sequent(ant,suc)
    def apply(ant:TraversableOnce[E], suc:TraversableOnce[E]) = new Sequent(ant.toList,suc.toList)
    def apply(ant:LinearSeq[E], suc:LinearSeq[E]) = new Sequent(ant.toList,suc.toList)
  }
}

