package at.logic.skeptik.judgment
package immutable

import at.logic.skeptik.expression.E
import collection.mutable.Stack
import at.logic.skeptik.expression.formula.Neg
  

class SeqSequent(val ant: Seq[E], val suc: Seq[E]) extends ASequent { 
  def +(f:E) = new SeqSequent(ant, suc :+ f)
  def +:(f:E) = new SeqSequent(ant :+ f, suc)
  def -(f:E) =  new SeqSequent(ant, suc.filterNot(_ == f))
  def -:(f:E) = new SeqSequent(ant.filterNot(_ == f), suc)
  
  
  
  
  def ++(s:SeqSequent) = new SeqSequent(ant ++ s.ant, suc ++ s.suc)
  def --(s:SeqSequent) = new SeqSequent(ant.filterNot(f => s.ant.exists(_ == f)), suc.filterNot(f => s.suc.exists(_ == f)))
  def -*(f:E) = new SeqSequent(ant, suc.filterNot(_ eq f)) 
  def -*:(f:E) = new SeqSequent(ant.filterNot(_ eq f), suc)  
  def --*(s:SeqSequent) = new SeqSequent(ant.filterNot(f => s.ant.exists(_ eq f)), suc.filterNot(f => s.suc.exists(_ eq f)))
  
  
  override def size = ((ant union suc).map(_.size) :\ 0)(_ + _ + 1) 
}

object SeqSequent {
  def apply(ant:Iterable[E])(suc:Iterable[E]) = new SeqSequent(ant.toSeq, suc.toSeq)
  def apply(ant:E*)(suc:E*) = new SeqSequent(ant, suc)
  def apply(s: TraversableOnce[E]) = {
    val ant = new Stack[E]; val suc = new Stack[E];
    for (f <- s) f match {
      case Neg(g) => ant.push(g)
      case _ => suc.push(f)
    }
    new SeqSequent(ant,suc)
  } 
}

