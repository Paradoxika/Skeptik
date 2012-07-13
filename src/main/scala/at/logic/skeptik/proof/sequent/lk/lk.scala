package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.expression.{E,Var}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression.position.Position
import at.logic.skeptik.prover.InferenceRule


class AxiomTaut(val mainLeft: E, val mainRight: E) extends SequentProof
with Nullary with NoImplicitContraction {
  override def mainFormulas = Sequent(mainLeft,mainRight)
  override def activeAncestry(f: E, premise: SequentProof) = throw new Exception("Active formulas in axioms have no ancestors.")
}

class Axiom(override val mainFormulas: Sequent) extends SequentProof
with Nullary with NoImplicitContraction {
  override def activeAncestry(f: E, premise: SequentProof) = throw new Exception("Active formulas in axioms have no ancestors.")
}

class WeakeningL(val premise:SequentProof, override val mainFormula :E)
extends SequentProof with Unary with NoAuxFormula
with SingleMainFormula with Left with NoImplicitContraction 


class AndL(val premise:SequentProof, val auxL:E, val auxR:E)
extends SequentProof with Unary with TwoAuxFormulas with BothInAnt
with SingleMainFormula with Left with NoImplicitContraction {
  val mainFormula = auxL ∧ auxR
}

class AndR(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E)
extends SequentProof with Binary with TwoAuxFormulas with OnePerSuccedent
with NoImplicitContraction with SingleMainFormula with Right  {
  val mainFormula = auxL ∧ auxR
}

class AllL(val premise:SequentProof, val aux:E, val v:Var, val position:Position)
extends SequentProof with Unary with SingleAuxFormula with InAnt
with SingleMainFormula with Left with NoImplicitContraction {
  val mainFormula = All(aux, v, position)
}

class ExR(val premise:SequentProof, val aux:E, val v:Var, val position:Position)
extends SequentProof with Unary with SingleAuxFormula with InSuc
with SingleMainFormula with Right with NoImplicitContraction {
  val mainFormula = Ex(aux, v, position)
}

trait EigenvariableCondition extends SequentProof {
  def eigenvar: Var
  require(!conclusionContext.ant.exists(e => (eigenvar occursIn e)) &&
          !conclusionContext.suc.exists(e => (eigenvar occursIn e)))
}

class AllR(val premise:SequentProof, val aux:E, val v:Var, val eigenvar:Var)
extends SequentProof with Unary with SingleAuxFormula with InSuc
with SingleMainFormula with Right with NoImplicitContraction
with EigenvariableCondition {
  val mainFormula = All(aux,v,eigenvar)
}

class ExL(val premise:SequentProof, val aux:E, val v:Var, val eigenvar:Var)
extends SequentProof with Unary with SingleAuxFormula with InAnt
with SingleMainFormula with Left with NoImplicitContraction 
with EigenvariableCondition {
  val mainFormula = Ex(aux,v,eigenvar)
}


abstract class AbstractCut
extends SequentProof with Binary with TwoAuxFormulas with LeftInSucRightInAnt 
with NoMainFormula {
  require(auxL == auxR)
}

class Cut(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E)
extends AbstractCut with NoImplicitContraction 

class CutIC(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E)
extends AbstractCut with ImplicitContraction 





object Axiom {
  def apply(conclusion: Sequent) = new Axiom(conclusion)
  def unapply(p: SequentProof) = p match {
    case p: Axiom => Some(p.conclusion)
    case _ => None
  }
}

object AxiomTaut extends InferenceRule[Sequent, SequentProof] {
  def apply(mainLeft: E, mainRight: E) = new AxiomTaut(mainLeft, mainRight)
  def unapply(p: SequentProof) = p match {
    case p: Axiom => Some(p.conclusion)
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: Sequent): Seq[Seq[Sequent]] = Seq(Seq())
  
  def apply(premises: Seq[SequentProof], conclusion: Sequent): Option[SequentProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 0 && conclusion.ant.length == 1 && conclusion.suc.length == 1 && conclusion.ant.head == conclusion.suc.head) 
      Some(new AxiomTaut(conclusion.ant.head, conclusion.suc.head))
    else None
  }
}

object AllR {
  def apply(premise:SequentProof, aux:E, v:Var, eigenvar:Var) = new AllR(premise,aux,v,eigenvar)
  def unapply(p: SequentProof) = p match {
    case p: AllR => Some((p.premise,p.aux,p.v,p.eigenvar))
    case _ => None
  }
}
object AllL {
  def apply(premise:SequentProof, aux:E, v:Var, p:Position) = new AllL(premise,aux,v,p)
  def unapply(p: SequentProof) = p match {
    case p: AllL => Some((p.premise,p.aux,p.v,p.position))
    case _ => None
  }
}
object AndL extends InferenceRule[Sequent, SequentProof] {
  def apply(premise: SequentProof, auxL:E, auxR:E) = new AndL(premise,auxL,auxR)
  def unapply(p: SequentProof) = p match {
    case p: AndL => Some((p.premise,p.auxL,p.auxR))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: Sequent): Seq[Seq[Sequent]] = { 
    for (main <- j.ant if main ?: And) yield {
      val (auxL, auxR) = main match {case And(aL,aR) => (aL,aR)}
      ( (auxL +: (auxR +: (main -*: j))) :: Nil ).toSeq
    }
  }
 
  // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  def apply(premises: Seq[SequentProof], conclusion: Sequent): Option[SequentProof] = { 
    if (premises.length == 1) {
      val premConc = premises.head.conclusion
      conclusion.ant.find(f => (f ?: And) && (! premConc.ant.contains(f))) match {
        case None => None
        case Some(And(aL,aR)) => {
          def findAux(f:E) = premConc.ant.find(aux => f == aux)
          (findAux(aL),findAux(aR)) match {
            case (Some(auxL),Some(auxR)) => {
              val proof = AndL(premises.head,auxL,auxR)
              require(proof.conclusion == conclusion)
              Some(proof)
            }
            case _ => None
          }
        } 
      }
    }
    else None
  }
}

object WeakeningL extends InferenceRule[Sequent, SequentProof] {
  def apply(premise: SequentProof, main:E) = new WeakeningL(premise,main)
  def unapply(p: SequentProof) = p match {
    case p: WeakeningL => Some((p.premise,p.mainFormula))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: Sequent): Seq[Seq[Sequent]] = { 
    for (main <- j.ant) yield ( (main -*: j) :: Nil ).toSeq
  }
 
  // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  def apply(premises: Seq[SequentProof], conclusion: Sequent): Option[SequentProof] = { 
    val premConc = premises.head.conclusion
    if (premises.length == 1 && 
        (conclusion supersequentOf premConc) && 
        conclusion.ant.length == premConc.ant.length + 1 && 
        conclusion.suc.length == premConc.suc.length) {
      
      conclusion.ant.find(! premConc.ant.contains(_)) match {
        case None => None
        case Some(mainFormula) => {
              val proof = WeakeningL(premises.head,mainFormula)
              require(proof.conclusion == conclusion)
              Some(proof)
        } 
      }
    }
    else None
  }
}


object AndR {
  def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new AndR(leftPremise,rightPremise,auxL,auxR)
  def unapply(p: SequentProof) = p match {
    case p: AndR => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}
object Cut {
  def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new Cut(leftPremise,rightPremise,auxL,auxR)
  def unapply(p: SequentProof) = p match {
    case p: Cut => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}

class AuxiliaryFormulaNotFoundException extends Exception

object CutIC {
  def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new CutIC(leftPremise,rightPremise,auxL,auxR)
  
  def apply(leftPremise: SequentProof, rightPremise: SequentProof, isPivot: E => Boolean) = (leftPremise.conclusion.suc.find(isPivot), rightPremise.conclusion.ant.find(isPivot)) match {
    case (Some(auxL), Some(auxR)) => new CutIC(leftPremise, rightPremise, auxL, auxR)
    case _ => throw new AuxiliaryFormulaNotFoundException
  } 
  
  def apply(premise1:SequentProof, premise2:SequentProof) = {
    def findPivots(p1:SequentProof, p2:SequentProof): Option[(E,E)] = {
      for (auxL <- p1.conclusion.suc; auxR <- p2.conclusion.ant) if (auxL == auxR) return Some(auxL,auxR)
      return None
    }
    findPivots(premise1,premise2) match {
      case Some((auxL,auxR)) => new CutIC(premise1,premise2,auxL,auxR)
      case None => findPivots(premise2,premise1) match {
        case Some((auxL,auxR)) => new CutIC(premise2,premise1,auxL,auxR)
        case None => throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
      }
    }
  }
  def unapply(p: SequentProof) = p match {
    case p: CutIC => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}

