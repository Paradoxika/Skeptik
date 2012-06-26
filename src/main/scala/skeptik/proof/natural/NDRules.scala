package skeptik.proof
package natural

import skeptik.expression._
import skeptik.expression.formula._
import skeptik.prover.InferenceRule
import collection.Set
import skeptik.judgment.{NaturalSequent,NamedE}


object nameFactory {
  private var counter = 0
  def apply():String = {counter += 1; "e" + counter}
}



abstract class NaturalDeductionProof(override val premises: List[NaturalDeductionProof])
extends Proof[NaturalSequent, NaturalDeductionProof]


class Assumption(val conclusion: NaturalSequent) extends NaturalDeductionProof(Nil) {
  require(conclusion.context.exists(_.expression == conclusion.e))
}

class ImpIntro(val premise: NaturalDeductionProof, val assumption: NamedE)
extends NaturalDeductionProof(premise::Nil) {
  require(premise.conclusion.context contains assumption)
  override val conclusion = new NaturalSequent(premise.conclusion.context - assumption, Imp(assumption.expression, premise.conclusion.e))
}

class ImpElim(val leftPremise:NaturalDeductionProof, val rightPremise:NaturalDeductionProof)
extends NaturalDeductionProof(leftPremise::rightPremise::Nil) {
  override val conclusion = (leftPremise.conclusion.e,rightPremise.conclusion.e) match {
    case (a,Imp(b,c)) if a == b => new NaturalSequent(leftPremise.conclusion.context ++ rightPremise.conclusion.context, c)
    case _ => throw new Exception("Implication Elimination Rule cannot be applied because the formulas do not match")
  }
}

object Assumption extends InferenceRule[NaturalSequent, NaturalDeductionProof] {
//  def apply(conclusion: NaturalSequent) = new Assumption(conclusion)
//  def unapply(p: NaturalDeductionProof) = p match {
//    case p: Assumption => Some(p.conclusion)
//    case _ => None
//  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent) = Seq(Seq())
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: NaturalSequent): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 0 && conclusion.context.exists(_.expression == conclusion.e)) Some(new Assumption(conclusion))
    else None
  }
}


object ImpIntro extends InferenceRule[NaturalSequent, NaturalDeductionProof] {
  def apply(premise: NaturalDeductionProof, assumption: NamedE) = new ImpIntro(premise, assumption)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpIntro => Some((p.premise, p.assumption))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent): Seq[Seq[NaturalSequent]] = j.e match {
    case Imp(a,b) => Seq(Seq(new NaturalSequent(j.context + NamedE(nameFactory(), a), b))) 
    case _ => Seq()
  } 
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: NaturalSequent): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 1) conclusion.e match {
      case Imp(a,b) => {
        if (b == premises(0).conclusion.e) premises(0).conclusion.context.find(_.expression == a) match {
          case Some(assumption) => Some(new ImpIntro(premises(0), assumption))
          case None => None
        }
        else None   
      }
      case _ => None
    }
    else None
  }
}


object ImpElim extends InferenceRule[NaturalSequent, NaturalDeductionProof] {
  def apply(leftPremise: NaturalDeductionProof, rightPremise: NaturalDeductionProof) = new ImpElim(leftPremise, rightPremise)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpElim => Some((p.leftPremise, p.rightPremise))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent) = (for (h <- j.context) yield h match {
    case NamedE(n,Imp(a,b)) if b == j => {
      Some(Seq(new NaturalSequent(j.context,a), new NaturalSequent(j.context,Imp(a,b))))
    }
    case _ => None
  }).filter(_ != None).map(_.get).toSeq 
 
  def apply(premises: Seq[NaturalDeductionProof], conclusion: NaturalSequent): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 2) {
      try {
        val proof = ImpElim(premises(0), premises(1))
        if (proof.conclusion == conclusion) Some(proof)
        else None
      }
      catch {case e: Exception => None}
    }
    else None
  }
}
