package at.logic.skeptik.judgment
package immutable

import at.logic.skeptik.expression.E
import collection.mutable.Stack
import at.logic.skeptik.expression.formula.Neg
  


/** A class for immutable sequents whose cedents are seqs.
 *
 *  @example {{{
 *  // Make an empty SetSequent via the companion object factory
 *  val s = SetSequent()()
 *  
 *  // Add formula f to the succedent of sequent s
 *  val s1 = s + f
 *  
 *  // Add formula f to the antecedent of sequent s
 *  val s2 = f +: s
 *  
 *  // Compute the union of two sequents
 *  val s3 = s1 union s2
 *  
 *  }}}
 *
 *  @author  Bruno Woltzenlogel Paleo
 *  @version 0.2
 *  @since   0.2
 */
class SeqSequent(val ant: Seq[E], val suc: Seq[E]) extends Sequent with SequentLike[SeqSequent] { 
  def +(f:E) = new SeqSequent(ant, suc :+ f)
  def +:(f:E) = new SeqSequent(ant :+ f, suc)
  def -(f:E) =  new SeqSequent(ant, suc.filterNot(_ == f))
  def -:(f:E) = new SeqSequent(ant.filterNot(_ == f), suc)
 
  def union(that: Sequent) = new SeqSequent(ant union that.ant.toSeq, suc union that.suc.toSeq)
  def diff(that: Sequent) = new SeqSequent(ant diff that.ant.toSeq, suc diff that.suc.toSeq)
  def intersect(that: Sequent) = new SeqSequent(ant intersect that.ant.toSeq, suc intersect that.suc.toSeq)  
  
  // ToDo: Think about what to do with these methods
  def -*(f:E) = new SeqSequent(ant, suc.filterNot(_ eq f)) 
  def -*:(f:E) = new SeqSequent(ant.filterNot(_ eq f), suc)  
  def --*(s:SeqSequent) = new SeqSequent(ant.filterNot(f => s.ant.exists(_ eq f)), suc.filterNot(f => s.suc.exists(_ eq f)))
}

object SeqSequent {
  def apply(ant:E*)(suc:E*) = new SeqSequent(ant, suc)
  
  @deprecated  //ToDo: this should be transformed into an implicit conversion
  def apply(s: TraversableOnce[E]) = {
    val ant = new Stack[E]; val suc = new Stack[E];
    for (f <- s) f match {
      case Neg(g) => ant.push(g)
      case _ => suc.push(f)
    }
    new SeqSequent(ant,suc)
  } 
}

