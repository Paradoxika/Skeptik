package at.logic.skeptik.proof.sequent
package resolution

import collection.mutable.{ HashMap => MMap, Set => MSet }
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents
import at.logic.skeptik.parser.ProofParserSPASS

class UnifyingResolutionMRR(override val leftPremise: SequentProofNode,override val rightPremise: SequentProofNode,
  override val auxL: E,override val auxR: E,override val leftClean: SequentProofNode)(implicit unifiableVariables: MSet[Var])
  extends UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftClean){

  override val conclusionContext = {
    val antecedent = leftClean.conclusion.ant.map(e => mgu(e)) ++
      (rightPremise.conclusion.ant.filter(_ != auxR)).map(e => mgu(e))
    val succedent = (leftClean.conclusion.suc.filter(_ != auxL)).map(e => mgu(e)) ++
      rightPremise.conclusion.suc.map(e => mgu(e))
    new Sequent(antecedent, succedent)
  }
}

object UnifyingResolutionMRR extends CanRenameVariables{
//  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, auxL: E, auxR: E)(implicit unifiableVariables: MSet[Var]) = new UnifyingResolutionMRR(leftPremise, rightPremise, auxL, auxR)
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {

    val cleanNodes = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
    val leftPremiseClean = cleanNodes._1
    val rightPremiseClean = cleanNodes._2

    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremiseClean.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)
    if (unifiablePairs.length > 0) {
      val (auxL, auxR) = unifiablePairs(0)
      new UnifyingResolutionMRR(leftPremise, rightPremiseClean, auxL, auxR, leftPremiseClean)
    } else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
    else throw new Exception("Resolution: the resolvent is ambiguous.")
  }
  def unapply(p: SequentProofNode) = p match {
    case p: UnifyingResolution => Some((p.leftPremise, p.rightPremise, p.auxL, p.auxR))
    case _ => None
  }
}
