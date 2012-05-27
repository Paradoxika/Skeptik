package ResK.proofs.naturalDeduction

import ResK.expressions._
import ResK.formulas._
import ResK.proofs.Proof
import ResK.provers.InferenceRuleWithSideEffects
import scala.collection.Set

case class NamedE(name:String, expression:E)

object nameFactory {
  private var counter = 0
  def apply():String = {counter += 1; "e" + counter}
}

object typeAliases {
  type Context = Set[NamedE]  
}
import typeAliases._

abstract class NaturalDeductionProof(name: String, override val premises: List[NaturalDeductionProof])
extends Proof[E, NaturalDeductionProof](name, premises) {
  def context: Context
}

class Assumption(val assumption: NamedE)(implicit val context: Context) extends NaturalDeductionProof("Ax",Nil) {
  require(context contains assumption)
  override val conclusion = assumption.expression
}

class ImpIntro(val premise: NaturalDeductionProof, val assumption: NamedE)
extends NaturalDeductionProof("ImpIntro",premise::Nil) {
  require(premise.context contains assumption)
  override val context = premise.context - assumption
  override val conclusion = Imp(assumption.expression, premise.conclusion)
}

class ImpElim(val leftPremise:NaturalDeductionProof, val rightPremise:NaturalDeductionProof)
extends NaturalDeductionProof("ImpElim", leftPremise::rightPremise::Nil) {
  override lazy val context = leftPremise.context ++ rightPremise.context
  override val conclusion = (leftPremise.conclusion,rightPremise.conclusion) match {
    case (a,Imp(b,c)) if a == b => c
    case _ => throw new Exception("Implication Elimination Rule cannot be applied because the formulas do not match")
  }
}

object Assumption extends InferenceRuleWithSideEffects[E, NaturalDeductionProof, Context] {
  def apply(assumption: NamedE)(implicit context: Context) = new Assumption(assumption)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: Assumption => Some(p.assumption, p.context)
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: E)(implicit context: Context): Seq[Seq[(Context, E)]] = Seq(Seq())
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: E)(implicit c: Context): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 0) c.find(_.expression == conclusion) match {
      case Some(namedE) => Some(new Assumption(namedE))
      case None => None
    } 
    else None
  }
}


object ImpIntro extends InferenceRuleWithSideEffects[E, NaturalDeductionProof, Context] {
  def apply(premise: NaturalDeductionProof, assumption: NamedE) = new ImpIntro(premise, assumption)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpIntro => Some((p.premise, p.assumption))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: E)(implicit c: Context): Seq[Seq[(Context,E)]] = j match {
    case i @ Imp(a,b) => Seq(Seq((c + NamedE(nameFactory(), a), b))) 
    case _ => Seq()
  } 
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: E)(implicit c: Context): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 1) conclusion match {
      case i @ Imp(a,b) => {
        if (b == premises(0).conclusion) premises(0).context.find(_.expression == a) match {
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


object ImpElim extends InferenceRuleWithSideEffects[E, NaturalDeductionProof, Context] {
  def apply(leftPremise: NaturalDeductionProof, rightPremise: NaturalDeductionProof) = new ImpElim(leftPremise, rightPremise)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpElim => Some((p.leftPremise, p.rightPremise))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: E)(implicit c: Context): Seq[Seq[(Context,E)]] = (for (h <- c) yield h match {
    case NamedE(n,Imp(a,b)) if b == j => {
      val left = a
      val right = Imp(a,b)
      Some(Seq((c,left),(c,right)))
    }
    case _ => None
  }).filter(_ != None).map(_.get).toSeq 
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: E)(implicit c: Context): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
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