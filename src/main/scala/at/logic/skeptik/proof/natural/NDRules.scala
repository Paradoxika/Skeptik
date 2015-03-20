package at.logic.skeptik.proof
package natural

import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula.{Imp}
import at.logic.skeptik.prover.{InferenceRule, SaturationInferenceRule}
import at.logic.skeptik.judgment.{NaturalSequent,NamedE}

object nameFactory {
  private var counter = 0
  def apply():String = {counter += 1; "e" + counter}
}

trait Nullary extends NaturalDeductionProofNode with GenNullary[NaturalSequent, NaturalDeductionProofNode]
trait Unary extends NaturalDeductionProofNode with GenUnary[NaturalSequent, NaturalDeductionProofNode]
trait Binary extends NaturalDeductionProofNode with GenBinary[NaturalSequent, NaturalDeductionProofNode]

abstract class NaturalDeductionProofNode
extends ProofNode[NaturalSequent, NaturalDeductionProofNode] {
  override def toString = name + "(" + conclusion + "," + premises.mkString(",") + ")" 
}


class Assumption(val context: Set[NamedE], val a: NamedE) 
extends NaturalDeductionProofNode with Nullary {
  require(context contains a)
  val conclusion = new NaturalSequent(context, a.expression)
}

class ImpIntro(val premise: NaturalDeductionProofNode, val assumption: NamedE)
extends NaturalDeductionProofNode with Unary {
  require(premise.conclusion.context contains assumption)
  val conclusion = new NaturalSequent(premise.conclusion.context - assumption, Imp(assumption.expression, premise.conclusion.e))
}

class ImpElim(val leftPremise:NaturalDeductionProofNode, val rightPremise:NaturalDeductionProofNode)
extends NaturalDeductionProofNode with Binary {
  override val conclusion = (leftPremise.conclusion.e,rightPremise.conclusion.e) match {
    case (a,Imp(b,c)) if a == b => new NaturalSequent(leftPremise.conclusion.context ++ rightPremise.conclusion.context, c)
    case _ => throw new Exception("Implication Elimination Rule cannot be applied because the formulas do not match")
  }
}

object Assumption extends InferenceRule[NaturalSequent, NaturalDeductionProofNode] {
  def apply(context: Set[NamedE], a: NamedE) = new Assumption(context, a)
  def unapply(p: NaturalDeductionProofNode) = p match {
    case p: Assumption => Some(p.context, p.a)
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent) = if (j.context.exists(_.expression == j.e)) Seq(Seq())
                                 else Seq()
  
  def apply(premises: Seq[NaturalDeductionProofNode], conclusion: NaturalSequent): Option[NaturalDeductionProofNode] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 0) conclusion.context.find(_.expression == conclusion.e) match {
      case Some(n) => Some(new Assumption(conclusion.context, n))
      case None => None
    }
    else None
  }
}


object ImpIntro 
extends InferenceRule[NaturalSequent, NaturalDeductionProofNode] 
with SaturationInferenceRule[NaturalSequent, NaturalDeductionProofNode] {
  def apply(premise: NaturalDeductionProofNode, assumption: NamedE) = new ImpIntro(premise, assumption)
  def unapply(p: NaturalDeductionProofNode) = p match {
    case p: ImpIntro => Some((p.premise, p.assumption))
    case _ => None
  }
  
  // applies the rule top-down exhaustively
  def apply(premise: Seq[NaturalDeductionProofNode]) : Seq[NaturalDeductionProofNode] = {
    (for (a <- premise.head.conclusion.context) yield { new ImpIntro(premise.head, a) }).toSeq
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent): Seq[Seq[NaturalSequent]] = j.e match {
    case Imp(a,b) => Seq(Seq(new NaturalSequent(j.context + NamedE(nameFactory(), a), b))) 
    case _ => Seq()
  } 
  
  // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  def apply(premises: Seq[NaturalDeductionProofNode], conclusion: NaturalSequent): Option[NaturalDeductionProofNode] = { 
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


trait DeepMatch {
  def deepMatch(f:E, g:E): Option[E] = f match {
    case Imp(a, b) if b == g => {
     //println("c: " + c)
     Some(f) 
    }
    case Imp(a, b @ Imp(_,_)) => {
      //println("going deeper")
      deepMatch(b, g) 
    }
    case z => {
      //println{"nothing left"}
      //println(z)
      None 
    }
  }
}

object ImpElim 
extends InferenceRule[NaturalSequent, NaturalDeductionProofNode] 
with SaturationInferenceRule[NaturalSequent, NaturalDeductionProofNode]
with DeepMatch {
  def apply(leftPremise: NaturalDeductionProofNode, rightPremise: NaturalDeductionProofNode) = new ImpElim(leftPremise, rightPremise)
  def unapply(p: NaturalDeductionProofNode) = p match {
    case p: ImpElim => Some((p.leftPremise, p.rightPremise))
    case _ => None
  }
 
  
  // applies the rule top-down exhaustively
  def apply(premises: Seq[NaturalDeductionProofNode]) : Seq[NaturalDeductionProofNode] = {
    val leftPremise = premises.head
    val rightPremise = premises.last
    (leftPremise.conclusion.e,rightPremise.conclusion.e) match {
      case (a,Imp(b,c)) if a == b => Seq( new ImpElim(leftPremise, rightPremise) )
      case _ => Seq()
    }
  }
  
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent) = (for (h <- j.context) yield {
    //println("h: " + h)
    //println("j.e: " + j.e)

    
    deepMatch(h.expression, j.e) match {
      case Some(c @ Imp(a,b)) => {
        Some(Seq(new NaturalSequent(j.context,a), new NaturalSequent(j.context,c)))
      }
      case _ => None
    }
  }).filter(_ != None).map(_.get).toSeq 
 
  // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  def apply(premises: Seq[NaturalDeductionProofNode], conclusion: NaturalSequent): Option[NaturalDeductionProofNode] = {
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
