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
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

    val cleanNodes = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
    val leftPremiseClean = cleanNodes._1

    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)
    if (unifiablePairs.length > 0) {
      
      val (auxL, auxR) = unifiablePairs(0)
      var ax = null.asInstanceOf[SequentProofNode]
      ax = new UnifyingResolutionMRR(leftPremise, rightPremise, auxL, auxR, leftPremiseClean)
        var con = Contraction(ax)(unifiableVariables)
        //If they're ever equal, contraction did nothing; discard the contraction
        while (!con.conclusion.equals(ax.conclusion)) {
          ax = con
          con = Contraction(ax)(unifiableVariables)
        }
      ax
    } else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
    else throw new Exception("Resolution: the resolvent is ambiguous.")
  }
  
  def apply(firstPremise: SequentProofNode, secondPremise: SequentProofNode, thirdPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    
        val con = Contraction(secondPremise)(unifiableVariables)
        val conRes =  UnifyingResolutionMRR(thirdPremise, con)(unifiableVariables)
        //Since all examples so far have the first two premises referencing the same line, I'm doing this:
        if (conRes.conclusion.suc.length == 0 && conRes.conclusion.suc.length == 0) {
          conRes
        } else {
          throw new MRRException("3-way MRR failed.")
        }
    
  }
  
  def unapply(p: SequentProofNode) = p match {
    case p: UnifyingResolution => Some((p.leftPremise, p.rightPremise, p.auxL, p.auxR))
    case _ => None
  }
}

  case class MRRException(error: String) extends Exception

