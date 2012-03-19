package ResK

object judgments {
  import scala.collection.TraversableOnce
  import scala.collection.immutable.{HashSet => ISet}
  import scala.collection.mutable.Stack
  import ResK.expressions._
  import ResK.logicalConstants._
  import ResK.utilities.prettyPrinting._
  import ResK.formulas._
  
  abstract class Judgment
  class Sequent(val ant:List[E], val suc:List[E]) extends Judgment {
    def contains(f:E) = (ant contains f) || (suc contains f)
    def supersequentOf(s:Sequent) = s.ant.forall(f => ant contains f) && s.suc.forall(f => suc contains f)
    def --(s:Sequent) = Sequent(ant -- s.ant, suc -- s.suc)
    def ++(s:Sequent) = Sequent(ant ++ s.ant, suc ++ s.suc)
    def +(f:E) = new Sequent(ant, f::suc)
    def +:(f:E) = new Sequent(f::ant, suc)
    def -(f:E) = new Sequent(ant, suc - f)
    def -:(f:E) = new Sequent(ant - f, suc)    
    
    def ==(s:Sequent) = (ant.toSet == s.ant.toSet) || (suc.toSet == s.suc.toSet)
    override def hashCode = 42*ant.toSet.hashCode + suc.toSet.hashCode
    override def toString = listToCSVString(ant) + " :- " + listToCSVString(suc)
    def toSet: ISet[E] = ISet() ++ ant.map(f => Neg(f)) ++ suc
  }
  object Sequent {
    def apply(ant:List[E], suc:List[E]) = new Sequent(ant,suc)
    def apply(ant:List[E], suc:E) = new Sequent(ant,suc::Nil)
    def apply(ant:E, suc:List[E]) = new Sequent(ant::Nil,suc)
    def apply() = new Sequent(Nil,Nil)
    def apply(s: TraversableOnce[E]) = {
      val ant = new Stack[E]; val suc = new Stack[E];
      for (f <- s) f match {
        case Neg(g) => ant.push(g)
        case _ => suc.push(f)
      }
      new Sequent(ant.toList,suc.toList)
    } 
  }
}

