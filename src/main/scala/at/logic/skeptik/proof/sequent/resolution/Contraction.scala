package at.logic.skeptik.proof.sequent
package resolution

import collection.mutable.{ HashMap => MMap, Set => MSet }
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents
import at.logic.skeptik.parser.ProofParserSPASS

class Contraction(val premise: SequentProofNode)(implicit unifiableVariables: MSet[Var])
  extends SequentProofNode with Unary with CanRenameVariables {

  //TODO: test these
  def conclusionContext = makeContextSeq()
  def auxFormulas = makeAuxFormulas()
  def mainFormulas = makeMainFormulas()

  def makeMainFormulas(): Sequent = {
    if (!contracted) {
      //nothing changed
      Sequent()()
    } else if (sucContracted) {
      val sFinal = Sequent()(sucContraction._2(0))
      sFinal
    } else {
      val sFinal = Sequent(antContraction._2(0))()
      sFinal
    }
  }

  def makeAuxFormulas(): Sequent = {
    if (!contracted) {
      //nothing changed
      Sequent()()
    } else if (sucContracted) {
      val sFinal = addSuccedents(sucContraction._2.toList)
      sFinal
    } else {
      val sFinal = addAntecedents(antContraction._2.toList)
      sFinal
    }
  }

  def makeContextSeq(): Sequent = {
    //if it's in the context, it must be in the premise's conclusion, but not in our list of contracted elements
    if (!contracted) {
      //nothing changed
      premise.conclusionContext
    } else if (sucContracted) {
      val sA = addAntecedents(premise.conclusion.ant.toList)
      val sS = addSuccedents(conclusion.ant.filter(e => sucContraction._2.contains(e)).toList)
      val sFinal = sA union sS
      sFinal
    } else {
      val sA = addAntecedents(conclusion.ant.filter(e => antContraction._2.contains(e)).toList)
      val sS = addSuccedents(premise.conclusion.suc.toList)
      val sFinal = sA union sS
      sFinal
    }
  }

  val antContraction = contract(premise.conclusion.ant)(unifiableVariables)
  val sucContraction = contract(premise.conclusion.suc)(unifiableVariables)

  val contraction = contractB(premise.conclusion)(unifiableVariables)

  val antContracted = antContraction._1.length > 0
  val sucContracted = sucContraction._1.length > 0
  val contracted = antContracted || sucContracted

  //  def newAnt = antContraction._1
  //  def newSuc = sucContraction._

  def newAnt = contraction._1
  def newSuc = contraction._2

  //Each contraction application contracts at most one pair of formulas
  override lazy val conclusion = {
    val antecedent = newAnt
    val succedent = newSuc
    new Sequent(antecedent, succedent)
  }

  def contractB(seq: Sequent)(implicit unifiableVariables: MSet[Var]): (Seq[E], Seq[E]) = {

    //    println("seq: " + seq)
    def isUnifiable(p: (E, E))(implicit unifiableVariables: MSet[Var]) = unify(p :: Nil)(unifiableVariables) match {
      case None => false
      case Some(_) => true
    }
    def isUnifiableWrapper(p: (E, E)) = {
      isUnifiable(p)(unifiableVariables) && !(p._1.equals(p._2))
    }

    val unifiablePairsC = (for (auxL <- seq.suc; auxR <- seq.suc) yield (auxL, auxR)).filter(isUnifiableWrapper)
    val unifiablePairsD = (for (auxL <- seq.ant; auxR <- seq.ant) yield (auxL, auxR)).filter(isUnifiableWrapper)
    val finalUnifiablePairsList = unifiablePairsC ++ unifiablePairsD

    if (finalUnifiablePairsList.length > 0) {
      val p = finalUnifiablePairsList.head

      //        val seqRight = Sequent()(p._2)
      //      val rightPremise = new Axiom(seqRight)
      //      val seqLeft = Sequent(p._1)()
      //      val leftPremise = new Axiom(seqLeft)
      //       val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
      //      val pp = (p._2, leftPremiseClean.conclusion.ant.head)
      //       println("pp: " + pp)

      val sub = unify(p :: Nil)(unifiableVariables) match {
        // case None => None
        case Some(u) => {
          //          println(pp)
          u
        }
      }
      //      println("sub: " + sub)
      val cleanSuc = (for (auxL <- seq.suc) yield sub(auxL))
      val cleanAnt = (for (auxL <- seq.ant) yield sub(auxL))
      //             println(cleanSuc)
      //             println(cleanAnt)

      //For testing only: ---
      //             val sA = addAntecedents(cleanAnt.distinct.toList)
      //      val sS = addSuccedents(cleanSuc.distinct.toList)
      //            val seqOut = sS union sA
      //      val axOut = Axiom(seqOut)
      //      println(axOut)
      // ---------

      (cleanAnt.distinct, cleanSuc.distinct)
    } else {
      (seq.ant, seq.suc)
    }
  }

  def contract(formulas: Seq[E])(implicit unifiableVariables: MSet[Var]): (Seq[E], Seq[E]) = {
    //Want to do pair-wise comparison for formulas in the antecedent of the premise

    //Check if the current head matches the rest of the antecedent
    def checkHead(h: E, t: Seq[E], start: Int): (Boolean, Int) = {
      if (t.length == 0) {
        return (false, -1)
      } else {
        val matched = contractPair(h, t.head, unifiableVariables)

        if (matched) {
          (true, start)
        } else {
          checkHead(h, t.tail, start + 1)
        }
      }
    }

    def checkAllPairs(formulaSeq: Seq[E], start: Int): (Int, Int) = {
      if (formulaSeq.length == 0) {
        return (-1, -1)
      }
      val h = formulaSeq.head
      //If the head did not match anything else, check the rest
      val result = checkHead(h, formulaSeq.tail, start + 1)
      if (!result._1) {
        checkAllPairs(formulaSeq.tail, start + 1)

        //if it did, we found a match, return true.
      } else {
        return (start, result._2)
      }
    }

    val firstPairLocations = checkAllPairs(formulas, 0)
    val first = firstPairLocations._1
    val second = firstPairLocations._2

    //Remove one of the ones we need to contract
    def removeNth(formulaSeq: Seq[E], n: Int, step: Int): List[E] = {
      if (n == step) {
        (formulaSeq.tail).toList
      } else {
        List(formulaSeq.head) ++ removeNth(formulaSeq.tail, n, step + 1)
      }
    }

    if (first != -1 && second != -1) {
      (removeNth(formulas, second, 0).toSeq, Seq[E](formulas(first), formulas(second)))
    } else {
      (formulas, Seq[E]())
    }

  }

  def contractPair(f1: E, f2: E, vars: MSet[Var]): Boolean = {
    def isUnifiable(p: (E, E)) = unify(p :: Nil)(vars) match {
      case None => false
      case Some(u) => {
        //        println("f1: " + f1)
        //        println("f2: " + f2)
        //        println("mgu: " + u)
        true
      }
    }
    isUnifiable((f1, f2))
  }

}

object Contraction extends FindDesiredSequent {
  def apply(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {
    new Contraction(premise)
  }
}
