package ResK.proofs

import ResK.judgments.Sequent
import ResK.expressions.{E,Var}
import ResK.formulas._
import ResK.positions._
import ResK.provers.InferenceRule


class AxiomTaut(val mainLeft: E, val mainRight: E) extends SequentProof("Ax",Nil,Map())
with NoImplicitContraction {
  override def mainFormulas = Sequent(mainLeft,mainRight)
  override def activeAncestry(f: E, premise: SequentProof) = throw new Exception("Active formulas in axioms have no ancestors.")
}

class Axiom(override val mainFormulas: Sequent) extends SequentProof("Ax",Nil,Map())
with NoImplicitContraction {
  override def activeAncestry(f: E, premise: SequentProof) = throw new Exception("Active formulas in axioms have no ancestors.")
}

class WeakeningL(val premise:SequentProof, override val mainFormula :E)
extends SequentProof("WeakeningL", premise::Nil, Map(premise -> Sequent(Nil,Nil)))
with SingleMainFormula with Left with NoImplicitContraction { 
  
}

class AndL(val premise:SequentProof, val auxL:E, val auxR:E)
extends SequentProof("AndL", premise::Nil, Map(premise -> Sequent(auxL::auxR::Nil,Nil)))
with SingleMainFormula with Left with NoImplicitContraction {
  override val mainFormula = And(auxL,auxR)
}

class AndR(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E)
extends SequentProof("AndR", leftPremise::rightPremise::Nil,
                      Map(leftPremise -> Sequent(Nil,auxL), rightPremise -> Sequent(Nil,auxR)))
with NoImplicitContraction with SingleMainFormula with Right  {
  override val mainFormula = And(auxL,auxR)
}

class AllL(val premise:SequentProof, val aux:E, val v:Var, val pl:List[IntListPosition])
extends SequentProof("AllL", premise::Nil,Map(premise -> Sequent(aux,Nil)))
with SingleMainFormula with Left with NoImplicitContraction {
  override val mainFormula = All(aux,v,pl)
}

class ExR(val premise:SequentProof, val aux:E, val v:Var, val pl:List[IntListPosition])
extends SequentProof("ExR", premise::Nil,Map(premise -> Sequent(Nil,aux)))
with SingleMainFormula with Right with NoImplicitContraction {
  override val mainFormula = Ex(aux,v,pl)
}

trait EigenvariableCondition extends SequentProof {
  val eigenvar: Var
  require(!conclusionContext.ant.exists(e => (eigenvar occursIn e)) &&
          !conclusionContext.suc.exists(e => (eigenvar occursIn e)))
}

class AllR(val premise:SequentProof, val aux:E, val v:Var, val eigenvar:Var)
extends SequentProof("AllR", premise::Nil,Map(premise -> Sequent(Nil,aux)))
with SingleMainFormula with Right with NoImplicitContraction
with EigenvariableCondition {
  override val mainFormula = All(aux,v,eigenvar)
}

class ExL(val premise:SequentProof, val aux:E, val v:Var, val eigenvar:Var)
extends SequentProof("ExL", premise::Nil,Map(premise -> Sequent(aux,Nil)))
with SingleMainFormula with Left with NoImplicitContraction 
with EigenvariableCondition {
  override val mainFormula = Ex(aux,v,eigenvar)
}


abstract class AbstractCut(val leftPremise:SequentProof, val rightPremise:SequentProof, 
                            val auxL:E, val auxR:E)
extends SequentProof("Cut",leftPremise::rightPremise::Nil,
                      Map(leftPremise -> Sequent(Nil,auxL),
                          rightPremise -> Sequent(auxR,Nil)))
with NoMainFormula {
  require(auxL == auxR)
}

class Cut(leftPremise:SequentProof, rightPremise:SequentProof, auxL:E, auxR:E)
extends AbstractCut(leftPremise, rightPremise, auxL, auxR)
with NoImplicitContraction 

class CutIC(leftPremise:SequentProof, rightPremise:SequentProof, auxL:E, auxR:E)
extends AbstractCut(leftPremise, rightPremise, auxL, auxR)
with ImplicitContraction 





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
  def apply(premise:SequentProof, aux:E, v:Var, pl:List[IntListPosition]) = new AllL(premise,aux,v,pl)
  def unapply(p: SequentProof) = p match {
    case p: AllL => Some((p.premise,p.aux,p.v,p.pl))
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
      val (auxL, auxR): (E,E) = main match {case And(aL,aR) => (aL,aR)}
      ( (auxL +: (auxR +: (main -: j))) :: Nil ).toSeq
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

//def apply(premises: Seq[P]) : Seq[P] 
}

object WeakeningL extends InferenceRule[Sequent, SequentProof] {
  def apply(premise: SequentProof, main:E) = new WeakeningL(premise,main)
  def unapply(p: SequentProof) = p match {
    case p: WeakeningL => Some((p.premise,p.mainFormula))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: Sequent): Seq[Seq[Sequent]] = { 
    for (main <- j.ant) yield ( (main -: j) :: Nil ).toSeq
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

//def apply(premises: Seq[P]) : Seq[P] 
}


object AndR {
  def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new AndR(leftPremise,rightPremise,auxL,auxR)
  def unapply(p: SequentProof) = p match {
    case p: AndR => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}
//ToDo: Companion objects for ExL and ExR are missing. They are not needed yet.
object Cut {
  def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new Cut(leftPremise,rightPremise,auxL,auxR)
  def unapply(p: SequentProof) = p match {
    case p: Cut => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}
object CutIC {
  def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new CutIC(leftPremise,rightPremise,auxL,auxR)
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

