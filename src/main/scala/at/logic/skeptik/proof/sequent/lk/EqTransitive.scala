package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.congruence.structure.EqW


/**
 * EqTransitive represents transitivity axioms
 * 
 * left side can be any transitivity chain of equalities and the right side is the equality between the first and last element of the chain
 */
class EqTransitive(mainFormulas: Sequent) extends TheoryAxiom(mainFormulas)

/**
 * companion object of EqTransitive
 * 
 * creates an EqTransitive object either from a full sequent (which should perhaps not be possible)
 * or an sequence of equations and two terms (semantics not checked)
 * or two equations representing the equality chain, where the implied equality is computed and
 * and exception is trown if there is none
 * 
 */
object EqTransitive {
  
  def apply(conclusion: Sequent) = new EqTransitive(conclusion)
  
  def apply(eqsLeft: Seq[EqW], t1: E, t2: E)(implicit eqReferences: MMap[(E,E),EqW]) = { // Semantics not checked!
    new EqTransitive(new Sequent(eqsLeft.map(_.equality),Seq(EqW(t1,t2).equality)))
  }
  
  def apply(eq1: EqW, eq2: EqW)(implicit eqReferences: MMap[(E,E),EqW] = MMap[(E,E),EqW]()) = {
    val (u1,u2,v1,v2) = (eq1.l,eq1.r,eq2.l,eq2.r)
    val (t1,t2) = 
      if (u1 == v1) (u2,v2)
      else if (u1 == v2) (u2,v1)
      else if (u2 == v1) (u1,v2)
      else if (u2 == v2) (u1,v1)
      else throw new Exception("Error occured while creating EQtransitive node: "+ eq1 + " and " + eq2 + " don't form a transitivity chain")
    val x = EqW(t1,t2).equality
    new EqTransitive(new Sequent(Seq(eq1.equality,eq2.equality),Seq(x)))
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqTransitive => Some(p.conclusion)
    case _ => None
  }
}
