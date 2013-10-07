package at.logic.skeptik.proof
package sequent

import collection.mutable.{HashMap => MMap, HashSet => MSet}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression.E

abstract class SequentProofNode
extends ProofNode[Sequent, SequentProofNode] {
  def auxFormulasMap: Map[SequentProofNode, Sequent]
  def mainFormulas : Sequent
  def conclusionContext : Sequent
  // The lazy modifier for "conclusion" is very important,
  // because "conclusion" calls methods that will only be overriden by subtraits and subclasses.
  override lazy val conclusion: Sequent = mainFormulas union conclusionContext
  override def toString():String = {
    this.conclusion.toString + " ~ " + this.hashCode()
  }
}

trait Nullary extends SequentProofNode with GenNullary[Sequent,SequentProofNode] {
  def auxFormulasMap = Map()
}

trait Unary extends SequentProofNode with GenUnary[Sequent,SequentProofNode] {
  def auxFormulas: Sequent
  def auxFormulasMap = Map(premise -> auxFormulas)
}

trait NoAuxFormula extends Unary { def auxFormulas = Sequent()() }

trait SingleAuxFormula { def aux: E }
trait InAnt extends Unary with SingleAuxFormula { def auxFormulas = Sequent(aux)() }
trait InSuc extends Unary with SingleAuxFormula { def auxFormulas = Sequent()(aux) }

trait TwoAuxFormulas { def auxL: E ; def auxR: E }
trait BothInAnt extends Unary with TwoAuxFormulas { def auxFormulas = Sequent(auxL,auxR)() }
trait BothInSuc extends Unary with TwoAuxFormulas { def auxFormulas = Sequent()(auxL,auxR) }
trait OnePerCedent extends Unary with TwoAuxFormulas { def auxFormulas = Sequent(auxL)(auxR) }

trait Binary extends SequentProofNode with GenBinary[Sequent,SequentProofNode] {  
  def leftAuxFormulas: Sequent
  def rightAuxFormulas: Sequent
  def auxFormulasMap = Map(leftPremise -> leftAuxFormulas, rightPremise -> rightAuxFormulas)
}

trait OnePerAntecedent extends Binary with TwoAuxFormulas {
  def leftAuxFormulas = Sequent(auxL)()
  def rightAuxFormulas = Sequent(auxR)()
}

trait OnePerSuccedent extends Binary with TwoAuxFormulas {
  def leftAuxFormulas = Sequent()(auxL)
  def rightAuxFormulas = Sequent()(auxR)
}

trait LeftInSucRightInAnt extends Binary with TwoAuxFormulas {
  def leftAuxFormulas = Sequent()(auxL)
  def rightAuxFormulas = Sequent(auxR)()
}


trait SingleMainFormula extends SequentProofNode {
  def mainFormula : E
}

trait Left  extends SingleMainFormula {override def mainFormulas = Sequent(mainFormula)()}
trait Right extends SingleMainFormula {override def mainFormulas = Sequent()(mainFormula)}

trait NoMainFormula extends SequentProofNode {
  override def mainFormulas = Sequent()()
}


trait NoImplicitContraction extends SequentProofNode {
  override def conclusionContext: Sequent = {
    val premiseContexts = premises.map(p => p.conclusion --* auxFormulasMap(p))
    if (premiseContexts.isEmpty) Sequent()()
    else (premiseContexts.head /: premiseContexts.tail) { (s1,s2) => s1 union s2 }
  }
}

trait ImplicitContraction extends SequentProofNode {
  override def conclusionContext: Sequent = {
    // val premiseContexts = premises.map(p => p.conclusion --* auxFormulasMap(p))
    val premiseContexts = premises.map(p => p.conclusion diff auxFormulasMap(p))
    val s = if (premiseContexts.isEmpty) Sequent()()
            else (premiseContexts.head /: premiseContexts.tail) { (s1,s2) => s1 union s2 }
    Sequent(s.ant.distinct:_*)(s.suc.distinct:_*)
  }
}


