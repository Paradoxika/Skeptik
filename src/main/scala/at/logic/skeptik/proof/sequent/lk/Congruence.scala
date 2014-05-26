package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.congruence.structure.EqW


/**
 * EqAxioms is the superclass of all equality axioms (reflexivity, transitivity and congruence)
 * equality axioms are special types of SequentProofNodes
 */

abstract class EqAxiom(override val mainFormulas: Sequent) extends SequentProofNode
  with Nullary with NoImplicitContraction {
  def getConclusionEq: E = {
    conclusion.suc.last
  }
}

/**
 * EqReflexive is an axiom with the conclusion ( |- u = u )
 * 
 * I'm not sure whether this axiom really has to be used
 */
class EqReflexive(override val mainFormulas: Sequent) extends EqAxiom(mainFormulas)

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
  def unapply(p: SequentProofNode) = p match {
    case p: EqReflexive => Some(p.conclusion)
    case _ => None
  }
}

/**
 * EqTransitive represents transitivity axioms
 * 
 * left side can be any transitivity chain of equalities and the right side is the equality between the first and last element of the chain
 */
class EqTransitive(override val mainFormulas: Sequent) extends EqAxiom(mainFormulas)

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
  
  def apply(eqsLeft: Seq[EqW], t1: E, t2: E, eqReferences: MMap[(E,E),EqW]) = { // Semantics not checked!
    new EqTransitive(new Sequent(eqsLeft.map(_.equality),Seq(EqW(t1,t2,eqReferences).equality)))
  }
  
  def apply(eq1: EqW, eq2: EqW, eqReferences: MMap[(E,E),EqW] = MMap[(E,E),EqW]()) = {
    val (u1,u2,v1,v2) = (eq1.l,eq1.r,eq2.l,eq2.r)
    val (t1,t2) = 
      if (u1 == v1) (u2,v2)
      else if (u1 == v2) (u2,v1)
      else if (u2 == v1) (u1,v2)
      else if (u2 == v2) (u1,v1)
      else throw new Exception("Error occured while creating EQtransitive node: "+ eq1 + " and " + eq2 + " don't form a transitivity chain")
    val x = EqW(t1,t2,eqReferences).equality
    new EqTransitive(new Sequent(Seq(eq1.equality,eq2.equality),Seq(x)))
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqTransitive => Some(p.conclusion)
    case _ => None
  }
}

/**
 * EqCongruent represents congruence axioms
 * 
 * axiom of the form ( a = b, f(a) = c |- f(b) = c )
 */

class EqCongruent(override val mainFormulas: Sequent) extends EqAxiom(mainFormulas)

/**
 * companion object of EqTransitive
 * 
 * creates an EqTransitive object from a sequent
 * or either one, two or a sequence of equations on the left and one right
 * the semantics are so far not checked in any of the cases
 */
object EqCongruent {
  def apply(conclusion: Sequent) = new EqCongruent(conclusion)
  def apply(expl: EqW, eq: EqW) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(Seq(expl.equality),Seq(eq.equality)))
  }
  def apply(expl1: EqW, expl2: EqW, eq: EqW) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(Seq(expl1.equality,expl2.equality),Seq(eq.equality)))
  }
  def apply(expls: Seq[EqW], eq: EqW) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(expls.map(_.equality),Seq(eq.equality)))
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqCongruent => Some(p.conclusion)
    case _ => None
  }
}