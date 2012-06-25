package skeptik.proof
package sequent

import collection.mutable.{HashMap => MMap, HashSet => MSet}
import skeptik.judgment.Sequent
import skeptik.expression.E

// TODO: (Bruno) passing arguments in the constructor of this abstract class makes it impossible
// to initialize these fields with traits. This leads to code duplication.
// It might be a good idea to transform these into def's.
abstract class SequentProof(name: String, 
                            override val premises: List[SequentProof],
                            val auxFormulas: Map[SequentProof, Sequent])
extends Proof[Sequent, SequentProof](name, premises) {
  require(premises.forall(p => p.conclusion supersequentOf auxFormulas(p)))
  // ancestry returns the subsequent of the given premise's conclusion
  // containing only ancestors of the given formula
  def ancestry(f: E, premise: SequentProof): Sequent = {
    if (mainFormulas.exists(_ eq f)) activeAncestry(f, premise)
    else contextAncestry(f,premise)
  }
  def activeAncestry(f: E, premise: SequentProof): Sequent
  def contextAncestry(f: E, premise: SequentProof): Sequent
  def mainFormulas : Sequent
  def conclusionContext : Sequent
  // The lazy modifier for "conclusion" is very important,
  // because "conclusion" calls methods that will only be overriden by subtraits and subclasses.
  override lazy val conclusion = mainFormulas ++ conclusionContext
}

trait SingleMainFormula extends SequentProof {
  def mainFormula : E
  override def activeAncestry(f:E,premise:SequentProof) = {
    require(f eq mainFormula); require(premises contains premise)
    auxFormulas.getOrElse(premise,Sequent())
  }
}

trait Left  extends SingleMainFormula {override def mainFormulas = Sequent(mainFormula,Nil)}
trait Right extends SingleMainFormula {override def mainFormulas = Sequent(Nil,mainFormula)}

trait NoMainFormula extends SequentProof {
  override def mainFormulas = Sequent()
  override def activeAncestry(f: E, premise: SequentProof) = throw new Exception("the given formula cannot be the main formula of this inference, because this inference has no main formula.")
}


trait NoImplicitContraction extends SequentProof {
  override def conclusionContext: Sequent = {
    val premiseContexts = premises.map(p => p.conclusion --* auxFormulas(p))
    premiseContexts match {
      case h::t => (h /: t)((s1,s2) => s1 ++ s2)
      case Nil => Sequent()
    }
  }
  override def contextAncestry(f: E, premise: SequentProof): Sequent = {
    require(conclusionContext.exists(_ eq f))
    require(premises contains premise)
    if (premise.conclusion.ant.exists(_ eq f)) Sequent(f,Nil)
    else if (premise.conclusion.suc.exists(_ eq f)) Sequent(Nil,f)
    else Sequent(Nil,Nil)
  }
}

trait ImplicitContraction extends SequentProof {
  private val contextAndAncestryAux: (Sequent, MMap[(E,SequentProof),Sequent]) = {
    // TODO: (Bruno) --* should be used instead of -- . 
    // However, doing this makes the proof compression algorithms stop working.
    // The bug is actually in the proof fixing codes (e.g. in line 30 in UnitLowering.scala)
    // The bug shall be properly fixed once all proof fixing codes are refactored into a single
    // method in a superclass or in a trait.
    // val context = premises.map(p => (p -> (p.conclusion --* auxFormulas(p)))).toMap
    val context = premises.map(p => (p -> (p.conclusion -- auxFormulas(p)))).toMap
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

    val contextAncestryMap = new MMap[(E,SequentProof),Sequent] // stores the ancestor relation
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
      computeConclusionAndAncestry(context(p).ant, antDuplicates, descendantsForAntDuplicates, conclusionContextAnt, Sequent(_,Nil))  
      computeConclusionAndAncestry(context(p).suc, sucDuplicates, descendantsForSucDuplicates, conclusionContextSuc, Sequent(Nil,_))
    }
    (Sequent(conclusionContextAnt.toList,conclusionContextSuc.toList), contextAncestryMap)
  }

  override val conclusionContext = contextAndAncestryAux._1
  override def contextAncestry(f: E, premise: SequentProof): Sequent = {
    require(conclusionContext contains f)
    require(premises contains premise)
    contextAndAncestryAux._2.getOrElse((f,premise),Sequent(Nil,Nil))
  }
}


