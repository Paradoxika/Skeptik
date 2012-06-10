package skeptik.proof
package sequent

import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import skeptik.judgment.Sequent
import skeptik.expression.E

// ToDo: passing arguments in the constructor of this abstract class makes it impossible
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
    val premiseContexts = premises.map(p => p.conclusion -- auxFormulas(p))
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
    val context = premises.map(p => (p -> (p.conclusion -- auxFormulas(p)))).toMap
    val antSeen = new MSet[E]
    val antDuplicates = new MSet[E]
    val sucSeen = new MSet[E]
    val sucDuplicates = new MSet[E]
    
    // ToDo: if a formula appears twice in the same premise, 
    // it will be implicitly contracted and will appear only once in the conclusion.
    // This is not alway the intended behaviour. See natural deduction, for example.
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
      for (f <- context(p).ant) {
        val descendant:E = {
          if (antDuplicates contains f) {
            if (descendantsForAntDuplicates contains f) {
              descendantsForAntDuplicates(f)
            }
            else {
              val desc = f.copy
              descendantsForAntDuplicates += (f -> desc)
              desc
            }
          }
          else f
        }
        conclusionContextAnt += descendant
        contextAncestryMap += ((descendant,p) -> Sequent(f,Nil))
      }
      for (f <- context(p).suc) {   //ToDo: remove code duplication for ant and suc
        val descendant:E = {
          if (sucDuplicates contains f) {
            if (descendantsForSucDuplicates contains f) {
              descendantsForSucDuplicates(f)
            }
            else {
              val desc = f.copy
              descendantsForSucDuplicates += (f -> desc)
              desc
            }
          }
          else f
        }
        conclusionContextSuc += descendant
        contextAncestryMap += ((descendant,p) -> Sequent(Nil,f))
      }
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


