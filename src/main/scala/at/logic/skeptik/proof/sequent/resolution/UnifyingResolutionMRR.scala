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

class UnifyingResolutionMRR(override val leftPremise: SequentProofNode, override val rightPremise: SequentProofNode,
  override val auxL: E, override val auxR: E, override val leftClean: SequentProofNode)(implicit unifiableVariables: MSet[Var])
  extends UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftClean) {

  override val conclusionContext = {
    val antecedent = leftClean.conclusion.ant.map(e => mgu(e)) ++
      (rightPremise.conclusion.ant.filter(_ != auxR)).map(e => mgu(e))
    val succedent = (leftClean.conclusion.suc.filter(_ != auxL)).map(e => mgu(e)) ++
      rightPremise.conclusion.suc.map(e => mgu(e))   
    new Sequent(antecedent, succedent)
  }

}

object UnifyingResolutionMRR extends CanRenameVariables with FindDesiredSequent {

  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, desired: Sequent)(implicit unifiableVariables: MSet[Var]) = {

    val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)

    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)

    if (unifiablePairs.length > 0) {
      findDesiredSequent(unifiablePairs, desired, leftPremise, rightPremise, leftPremiseClean, true)
    } else if (unifiablePairs.length == 0) {
      System.err.println("left:    " + leftPremise)
      System.err.println("right:   " + rightPremise)
      System.err.println("desired: " + desired)
      throw new MRRException("Resolution (MRR): the conclusions of the given premises are not resolvable.")
    } else {
      //Should never really be reached in this constructor
      throw new MRRException("Resolution (MRR): the resolvent is ambiguous.")
    }
  }

  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

    val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)

    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)

    if (unifiablePairs.length == 1) {

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
    } else if (unifiablePairs.length == 0) throw new MRRException("Resolution (MRR): the conclusions of the given premises are not resolvable.")
    else throw new MRRException("Resolution: the resolvent is ambiguous.")
  }

  def apply(firstPremise: SequentProofNode, secondPremise: SequentProofNode, thirdPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

    val con = Contraction(secondPremise)(unifiableVariables)
    val conRes = UnifyingResolutionMRR(thirdPremise, con)(unifiableVariables)
    //Since all examples so far have the first two premises referencing the same line, I'm doing this:
    if (conRes.conclusion.suc.length == 0 && conRes.conclusion.suc.length == 0) {
      conRes
    } else {
      throw new MRRException("3-way MRR failed.")
    }

  }

  def apply(firstPremise: SequentProofNode, secondPremise: SequentProofNode,
    thirdPremise: SequentProofNode, desired: Sequent)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    //Note that it's assumed that firstPremise = secondPremise when this is called, and that each
    //has formulas in exactly one of it's antecedent or succedent.
    //(this is a very specific case of resolution)

    assert(firstPremise.conclusion eq secondPremise.conclusion)

    if (firstPremise.conclusion.ant.length > 0 && firstPremise.conclusion.suc.length == 0) {
      val newDesired = Sequent(firstPremise.conclusion.ant.head)()
      val firstRes = UnifyingResolutionMRR(thirdPremise, secondPremise, newDesired)(unifiableVariables)
      val secondRes = UnifyingResolutionMRR(thirdPremise, firstRes, desired)(unifiableVariables)
      //Since all examples so far have the first two premises referencing the same line, I'm doing this:
      if (secondRes.conclusion.suc.length == 0 && firstRes.conclusion.suc.length == 0) {
        secondRes
      } else {
        throw new MRRException("3-way MRR failed (with desired sequent).")
      }
    } else if(firstPremise.conclusion.suc.length > 0 && firstPremise.conclusion.ant.length == 0) {
      val newDesired = Sequent()(firstPremise.conclusion.suc.head)
      val firstRes = UnifyingResolutionMRR(thirdPremise, secondPremise, newDesired)(unifiableVariables)
      val secondRes = UnifyingResolutionMRR(thirdPremise, firstRes, desired)(unifiableVariables)
      //Since all examples so far have the first two premises referencing the same line, I'm doing this:
      if (secondRes.conclusion.ant.length == 0 && firstRes.conclusion.ant.length == 0) {
        secondRes
      } else {
        throw new MRRException("3-way MRR failed (with desired sequent).")
      }
    } else {
       throw new MRRException("3-way MRR failed: usage assumption failed (with desired sequent).")
    }

  }

  
  def apply(premises: List[SequentProofNode], desired: Sequent)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
	  //Find the special node
      val repeats = premises.diff(premises.distinct).distinct
      require(repeats.size == 1)
      var special = repeats.head
      
      require(desired.logicalSize == 0) //for now, only for concluding proofs.
      val others = repeats.filterNot(_ eq special)
      
      for(p <- others){
        special = UnifyingResolution(special, p)
      }
      
      assert(special.conclusion.logicalSize == 0)
      special
    
  }  
  
  def unapply(p: SequentProofNode) = p match {
    case p: UnifyingResolutionMRR => Some((p.leftPremise, p.rightPremise, p.auxL, p.auxR))
    case _ => None
  }
}

case class MRRException(error: String) extends Exception

