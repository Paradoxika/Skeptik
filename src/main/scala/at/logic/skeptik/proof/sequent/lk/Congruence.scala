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

/**
 * EqCongruent represents congruence axioms
 * 
 * axiom of the form ( a = b, f(a) = c |- f(b) = c )
 */

class EqCongruent(mainFormulas: Sequent) extends TheoryAxiom(mainFormulas)

/**
 * companion object of EqTransitive
 * 
 * creates an EqTransitive object from a sequent
 * or either one, two or a sequence of equations on the left and one right
 * the semantics are so far not checked in any of the cases
 */
object EqCongruent {
  def apply(conclusion: Sequent): EqCongruent = {
    implicit val eqReferences = MMap[(E,E),EqW]()
    val singleSuc = conclusion.suc.size == 1
    require(singleSuc)
    val isEq = EqW.isEq(conclusion.suc.last)
    require(isEq)
    val eq = EqW(conclusion.suc.last)
    val (leftSub,rightSub) = (subterms(eq.l),subterms(eq.r))
    require(leftSub.size == rightSub.size)
    val correct = (leftSub zip rightSub).forall({tuple => 
      conclusion.ant.exists(lit => EqW.isEq(lit) && EqW(lit) == EqW(tuple._1,tuple._2))
    })
    require(correct)
    new EqCongruent(conclusion)
  }
  def apply(expl: Seq[E], eq: E): EqCongruent = { //Semantics are not checked (yet)
    this(new Sequent(expl,Seq(eq)))
  }
  def apply(expl: EqW, eq: EqW): EqCongruent = { //Semantics are not checked (yet)
    this(new Sequent(Seq(expl.equality),Seq(eq.equality)))
  }
  def apply(expl1: EqW, expl2: EqW, eq: EqW): EqCongruent = { //Semantics are not checked (yet)
    this(new Sequent(Seq(expl1.equality,expl2.equality),Seq(eq.equality)))
  }
  def apply(expls: Seq[EqW], eq: EqW): EqCongruent = { //Semantics are not checked (yet)
    this(new Sequent(expls.map(_.equality),Seq(eq.equality)))
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqCongruent => Some(p.conclusion)
    case _ => None
  }
  
  def subterms(term: E): Seq[E] = term match {
    case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
    case _ => Seq()
  }
  
  def uncurriedTerms(term: E): Seq[E] = term.t match {
    case Arrow(_,_) => {
      term match {
        case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
        case _ => Seq()
      }
    }
    case _ => Seq(term)
  }
}

class EqSymmetry(mainFormulas: Sequent) extends TheoryAxiom(mainFormulas)

object EqSymmetry {
  def apply(eq: EqW) = {
    new EqSymmetry(new Sequent(Seq(eq.equality),Seq(eq.reverseEquality)))
  }

  def unapply(p: SequentProofNode) = p match {
    case p: EqSymmetry => Some(p.conclusion)
    case _ => None
  }
}