package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.congruence.structure.EqW


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
