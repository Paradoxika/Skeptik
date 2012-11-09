package at.logic.skeptik.proof
package sequent

import collection.mutable.{HashMap => MMap, HashSet => MSet}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression.E

abstract class SequentProofNode
extends ProofNode[Sequent, SequentProofNode] {
  require(premises.forall(p => auxFormulasMap(p) subsequentOf p.conclusion ))
  // ancestry returns the subsequent of the given premise's conclusion
  // containing only ancestors of the given formula
  def ancestry(f: E, premise: SequentProofNode): Sequent = {
    if (mainFormulas.ant.exists(_ eq f) || mainFormulas.suc.exists(_ eq f)) activeAncestry(f, premise)
    else contextAncestry(f,premise)
  }
  def activeAncestry(f: E, premise: SequentProofNode): Sequent
  def contextAncestry(f: E, premise: SequentProofNode): Sequent
  def auxFormulasMap: Map[SequentProofNode, Sequent]
  def mainFormulas : Sequent
  def conclusionContext : Sequent
  // The lazy modifier for "conclusion" is very important,
  // because "conclusion" calls methods that will only be overriden by subtraits and subclasses.
  override lazy val conclusion: Sequent = mainFormulas union conclusionContext
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
  override def activeAncestry(f:E,premise:SequentProofNode) = {
    require(f eq mainFormula); require(premises contains premise)
    auxFormulasMap.getOrElse(premise,Sequent()())
  }
}

trait Left  extends SingleMainFormula {override def mainFormulas = Sequent(mainFormula)()}
trait Right extends SingleMainFormula {override def mainFormulas = Sequent()(mainFormula)}

trait NoMainFormula extends SequentProofNode {
  override def mainFormulas = Sequent()()
  override def activeAncestry(f: E, premise: SequentProofNode): Sequent = throw new Exception("the given formula cannot be the main formula of this inference, because this inference has no main formula.")
}


trait NoImplicitContraction extends SequentProofNode {
  override def conclusionContext: Sequent = {
    val premiseContexts = premises.map(p => p.conclusion --* auxFormulasMap(p))
    premiseContexts match {
      case h::t => (h /: t)((s1,s2) => s1 union s2)
      case Nil => Sequent()()
    }
  }
  override def contextAncestry(f: E, premise: SequentProofNode): Sequent = {
    require(conclusionContext.ant.exists(_ eq f) || conclusionContext.suc.exists(_ eq f))
    require(premises contains premise)
    if (premise.conclusion.ant.exists(_ eq f)) Sequent(f)()
    else if (premise.conclusion.suc.exists(_ eq f)) Sequent()(f)
    else Sequent()()
  }
}

trait ImplicitContraction extends SequentProofNode {
  private val contextAndAncestryAux: (Sequent, MMap[(E,SequentProofNode),Sequent]) = {
    // ToDo : (B) --* should be used instead of -- .
    // However, doing this makes the proof compression algorithms stop working.
    // The bug is actually in the proof fixing codes (e.g. in line 30 in UnitLowering.scala)
    // The bug shall be properly fixed once all proof fixing codes are refactored into a single
    // method in a superclass or in a trait.
    // val context = premises.map(p => (p -> (p.conclusion --* auxFormulas(p)))).toMap
    val context = premises.map(p => (p -> (p.conclusion diff auxFormulasMap(p)))).toMap
    val antSeen = new MSet[E]
    val antDuplicates = new MSet[E]
    val sucSeen = new MSet[E]
    val sucDuplicates = new MSet[E]
    
    for (p <- premises) {
      for (f <- context(p).ant) {
        if (antSeen contains f) antDuplicates += f
        else antSeen += f
      }
      for (f <- context(p).suc) {
        if (sucSeen contains f) sucDuplicates += f
        else sucSeen += f
      }
    }

    val contextAncestryMap = new MMap[(E,SequentProofNode),Sequent] // stores the ancestor relation
    val conclusionContextAnt = new MSet[E] // stores the formulas that will go into the antecedent of the conclusion context
    val conclusionContextSuc = new MSet[E] // stores the formulas that will go into the succedent of the conclusion context
    val descendantsForAntDuplicates = new MMap[E,E] // stores the new copy that will serve as the contraction for several duplicates in the antecedent.
    val descendantsForSucDuplicates = new MMap[E,E] // stores the new copy that will serve as the contraction for several duplicates in the succedent.
    for (p <- premises) {
      def computeConclusionAndAncestry(cedent: Iterable[E], 
                                       duplicates: MSet[E], 
                                       descendantsForDuplicates: MMap[E,E],
                                       conclusionContextCedent: MSet[E], 
                                       s: E => Sequent) = {
        for (f <- cedent) {
          val descendant:E = {
            if (duplicates contains f) {
              if (descendantsForDuplicates contains f) {
                descendantsForDuplicates(f)
              }
              else {
                val desc = f.copy
                descendantsForDuplicates += (f -> desc)
                desc
              }
            }
            else f
          }
          conclusionContextCedent += descendant
          contextAncestryMap += ((descendant,p) -> s(f))
        }
      }
      computeConclusionAndAncestry(context(p).ant, antDuplicates, descendantsForAntDuplicates, conclusionContextAnt, Sequent(_)())  
      computeConclusionAndAncestry(context(p).suc, sucDuplicates, descendantsForSucDuplicates, conclusionContextSuc, Sequent()(_))
    }
    (Sequent(conclusionContextAnt.toSeq : _*)(conclusionContextSuc.toSeq : _*), contextAncestryMap)
  }

  override val conclusionContext = contextAndAncestryAux._1
  override def contextAncestry(f: E, premise: SequentProofNode): Sequent = {
    require((conclusionContext.ant contains f) || (conclusionContext.suc contains f))
    require(premises contains premise)
    contextAndAncestryAux._2.getOrElse((f,premise),Sequent()())
  }
}


