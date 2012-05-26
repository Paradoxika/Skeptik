package ResK.proofs.naturalDeductionWithSequentNotation

import ResK.judgments.Sequent
import ResK.expressions.E
import ResK.formulas._
import ResK.proofs.{SequentProof,NoImplicitContraction,ImplicitContraction,SingleMainFormula,Right}
import ResK.provers.InferenceRule

object typeAliases {
  type NaturalDeductionProof = SequentProof
}
import typeAliases._

class Axiom(val leftSide: List[E], val c: E) extends NaturalDeductionProof("Ax",Nil,Map())
with NoImplicitContraction {
  require(leftSide contains c)
  override def mainFormulas = Sequent(leftSide,c)
  override def activeAncestry(f: E, premise: SequentProof) = throw new Exception("Active formulas in axioms have no ancestors.")
}

class ImpIntro(val premise: SequentProof, val auxL: E) 
extends NaturalDeductionProof("ImpIntro",premise::Nil, Map(premise -> Sequent(auxL,premise.conclusion.suc.head)))
with SingleMainFormula with Right with NoImplicitContraction {
  override val mainFormula = Imp(auxL,premise.conclusion.suc.head)
}

// ToDo: Maybe the trait ImplicitContraction is not exactly what is needed here. Check! 
class ImpElim(val leftPremise:SequentProof, val rightPremise:SequentProof)
extends NaturalDeductionProof("ImpElim", leftPremise::rightPremise::Nil,
                     Map(leftPremise -> Sequent(Nil,leftPremise.conclusion.suc.head), rightPremise -> Sequent(Nil,rightPremise.conclusion.suc.head)))
with ImplicitContraction with SingleMainFormula with Right  {
  override val mainFormula = (leftPremise.conclusion.suc.head,rightPremise.conclusion.suc.head) match {
    case (a,Imp(b,c)) if a == b => c
    case _ => throw new Exception("Implication Elimination Rule cannot be applied because the formulas do not match")
  }
}

object Axiom extends InferenceRule[Sequent, NaturalDeductionProof] {
  def apply(leftSide: List[E], c: E) = new Axiom(leftSide, c)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: Axiom => Some(p.leftSide,p.c)
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: Sequent): Seq[Seq[Sequent]] = Seq(Seq())
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: Sequent): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 0 && conclusion.suc.length == 1 && (conclusion.ant contains conclusion.suc.head))
      Some(new Axiom(conclusion.ant, conclusion.suc.head))
    else None
  }
}


object ImpIntro extends InferenceRule[Sequent, NaturalDeductionProof] {
  def apply(premise: NaturalDeductionProof, auxL: E) = new ImpIntro(premise, auxL)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpIntro => Some((p.premise, p.auxL))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: Sequent): Seq[Seq[Sequent]] = j.suc.head match {
    case i @ Imp(a,b) => Seq(Seq((a +: (j - i)) + b))
    case _ => Seq()
  } 
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: Sequent): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 1 && conclusion.suc.length == 1) conclusion.suc.head match {
      case i @ Imp(a,b) => {
        val premise = premises.head
        if (b == premise.conclusion.suc.head) premise.conclusion.ant.find(_ == a) match {
          case Some(auxL) => Some(new ImpIntro(premise, auxL))
          case None => None
        }
        else None   
      }
      case _ => None
    }
    else None
  }
}


object ImpElim extends InferenceRule[Sequent, NaturalDeductionProof] {
  def apply(leftPremise: NaturalDeductionProof, rightPremise: NaturalDeductionProof) = new ImpElim(leftPremise, rightPremise)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpElim => Some((p.leftPremise, p.rightPremise))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: Sequent): Seq[Seq[Sequent]] = (for (h <- j.ant) yield h match {
    case Imp(a,b) if b == j.suc.head => {
      val left = (h -: j) - b + a
      val right = Sequent(Imp(a,b),Imp(a,b))
      Some(Seq(left,right))
    }
    case _ => None
  }).filter(_ != None).map(_.get) 
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: Sequent): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 2 && conclusion.suc.length == 1) {
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