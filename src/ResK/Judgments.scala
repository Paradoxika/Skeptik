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
    def exists(p:E=>Boolean) = ant.exists(p) || suc.exists(p)
    def supersequentOf(s:Sequent) = s.ant.forall(f => ant contains f) && s.suc.forall(f => suc contains f)
    def --(s:Sequent) = Sequent(ant -- s.ant, suc -- s.suc) // ToDo: this needs to be carefully fixed, because now equals was overriden
    def ++(s:Sequent) = Sequent(ant ++ s.ant, suc ++ s.suc)
    def +(f:E) = new Sequent(ant, f::suc)
    def +:(f:E) = new Sequent(f::ant, suc)
    def -(f:E) = new Sequent(ant, suc - f) // ToDo: this needs to be carefully fixed, because now equals was overriden
    def -:(f:E) = new Sequent(ant - f, suc) // ToDo: this needs to be carefully fixed, because now equals was overriden    
    
    override def equals(v:Any) = v match {		
        case that:Sequent => (that canEqual this) && (ant.toSet == that.ant.toSet) && (suc.toSet == that.suc.toSet)	
        case _ => false		
    }		
    def canEqual(other: Any) = other.isInstanceOf[Sequent]
    
    override def hashCode = 42*ant.toSet.hashCode + suc.toSet.hashCode
    override def toString = listToCSVString(ant) + " :- " + listToCSVString(suc)
    def toSet: ISet[E] = ISet() ++ ant.map(f => Neg(f)) ++ suc
  }
  object Sequent {
    def apply(ant:List[E], suc:List[E]) = new Sequent(ant,suc)
    def apply(ant:List[E], suc:E) = new Sequent(ant,suc::Nil)
    def apply(ant:E, suc:List[E]) = new Sequent(ant::Nil,suc)
    def apply(ant:E, suc:E) = new Sequent(ant::Nil,suc::Nil)
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

