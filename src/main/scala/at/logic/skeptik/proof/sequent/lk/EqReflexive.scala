package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.congruence.structure.EqW


/**
 * EqReflexive is an axiom with the conclusion ( |- u = u )
 * 
 * I'm not sure whether this axiom really has to be used
 */
class EqReflexive(mainFormulas: Sequent) extends TheoryAxiom(mainFormulas)

/**
 * companion object of EqReflexive
 * 
 * creates an EqReflexive object either from a full sequent (which should perhaps not be possible)
 * or an expression, for which it is checked whether it is of the form (u = u) and an Exception is thrown if not
 */
object EqReflexive {
  def apply(conclusion: Sequent) = new EqReflexive(conclusion)
  def apply(expr: EqW, eqReferences: MMap[(E,E),EqW]) = {
    if (expr.l == expr.r) {
        val x = eqReferences.getOrElse((expr.l,expr.l), expr).equality
        new EqReflexive(new Sequent(Seq(),Seq(x)))
    }
    else throw new Exception("Error occured while creating EQReflexive node: "+ expr + " which is not an instance of reflexivity")
  }
  def apply(e: E)(implicit eqReferences: MMap[(E,E),EqW]) = {
    new EqReflexive(new Sequent(Seq(),Seq(EqW(e,e).equality)))
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqReflexive => Some(p.conclusion)
    case _ => None
  }
}