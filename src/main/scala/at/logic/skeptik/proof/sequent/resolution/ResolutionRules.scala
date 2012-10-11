package at.logic.skeptik.proof.sequent
package resolution

import collection.mutable.{HashMap => MMap}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression.{Var,E}
import at.logic.skeptik.algorithm.unifier.{MartelliMontanari => unify}


class R(val leftPremise:SequentProofNode, val rightPremise:SequentProofNode,
          val auxL:E, val auxR:E)(implicit unifiableVariables: Set[Var])
extends SequentProofNode with Binary
with NoMainFormula {
  val leftAuxFormulas = Sequent()(auxL)
  val rightAuxFormulas = Sequent(auxR)()
  val mgu = unify((auxL,auxR)::Nil) match {
    case None => throw new Exception("Resolution: given premise clauses are not resolvable.")
    case Some(u) => u
  }
  private val ancestryMap = new MMap[(E,SequentProofNode),Sequent]
  override val conclusionContext = {
    def descendant(e:E, p:SequentProofNode, anc: Sequent) = {val eS = mgu(e); ancestryMap += ((eS,p) -> anc); eS }
    val antecedent = leftPremise.conclusion.ant.map(e=>descendant(e,leftPremise,Sequent(e)())) ++
                    (rightPremise.conclusion.ant.filter(_ != auxR)).map(e=>descendant(e,rightPremise,Sequent(e)()))
    val succedent = (leftPremise.conclusion.suc.filter(_ != auxL)).map(e=>descendant(e,leftPremise,Sequent()(e))) ++
                    rightPremise.conclusion.suc.map(e=>descendant(e,rightPremise,Sequent()(e)))
    new Sequent(antecedent, succedent)
  }
  override def contextAncestry(f:E,premise:SequentProofNode) = {
    require((conclusion.ant contains f) || (conclusion.suc contains f))
    require(premises contains premise)
    ancestryMap.getOrElse((f,premise),Sequent()())
  }
}


object R {
  def apply(leftPremise:SequentProofNode, rightPremise:SequentProofNode, auxL:E, auxR:E)(implicit unifiableVariables:Set[Var]) = new R(leftPremise, rightPremise, auxL, auxR)
  def apply(leftPremise:SequentProofNode, rightPremise:SequentProofNode)(implicit unifiableVariables:Set[Var]) = {
    def isUnifiable(p:(E,E)) = unify(p::Nil)(unifiableVariables) match {
        case None => false
        case Some(_) => true
      }
    val unifiablePairs = (for (auxL <- leftPremise.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL,auxR)).filter(isUnifiable)
    if (unifiablePairs.length > 0) {
      val (auxL,auxR) = unifiablePairs(0)
      new R(leftPremise, rightPremise, auxL, auxR)
    }
    else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
    else throw new Exception("Resolution: the resolvent is ambiguous.")
  }
  def unapply(p:SequentProofNode) = p match {
    case p: R => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}
