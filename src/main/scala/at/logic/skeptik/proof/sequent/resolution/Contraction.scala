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
  extends SequentProofNode with Unary
  with NoMainFormula {

  //TODO: define this?
  def auxFormulas = ???

  override val conclusionContext = {
    val antecedent = premise.conclusion.ant
    val succedent = premise.conclusion.suc
    new Sequent(antecedent, succedent)
  }
}

object Contraction {
  def apply(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {
    println(contract(premise)(unifiableVariables))
    new Contraction(premise) //TODO: change this to the real thing
  }

  def contract(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): List[Substitution] = {
    //Want to do pair-wise comparison for formulas in the antecedent of the premise
    val ant = premise.conclusion.ant

    var change = null.asInstanceOf[List[Substitution]]

    //Check if the current head matches the rest of the antecedent
    def checkHead(h: E, t: Seq[E]): Boolean = {
      if (t.length == 0) {
        return false
      } else {
        val (replacements, matched) = contractPair(h, t.head)
        if (matched) {
          change = replacements
          matched
        } else {
          checkHead(h, t.tail)
        }
      }
    }

    def checkAllPairs(ant: Seq[E]): Boolean = {
      if (ant.length == 0) {
        return false
      }
      val h = ant.head
      //If the head did not match anything else, check the rest
      if (!checkHead(h, ant.tail)) {
        checkAllPairs(ant.tail)

        //if it did, we found a match, return true.
      } else {
        return true
      }
    }

    checkAllPairs(ant)
    change

  }

  def contractPair(f1: E, f2: E): (List[Substitution], Boolean) = f1 match {
    //if f1 is an App
    case App(e1, e2) => {
      f2 match {
        //see if f2 is also an App
        case App(e3, e4) => {

          //if it is, check if e1 and e3 are the same
          val (firstMaps, firstBool) = contractPair(e1, e3)

          //if so, check e2 and e4
          if (firstBool) {
            val (secondMaps, secondBool) = contractPair(e2, e4)

            //if it is, return the total list of substitutions and true; else return false
            if (secondBool) {
              (firstMaps ++ secondMaps, true)
            } else {
              (List[Substitution](), false)
            }

            //if not, return false
          } else {
            (List[Substitution](), false)
          }
        }
        //If not, it's something else, and clearly not a contraction
        case _ => (List[Substitution](), false)
      }
    }
    case Abs(v1, e1) => {
      f2 match {
        case Abs(v2, e2) => {

          val (firstMaps, firstBool) = contractPair(e1, e2)
          if (firstBool) {
            val hasLowerCase1 = v1.name.exists(_.isLower)
            val notAnInt1 = v1.name.charAt(0).isLetter
            val hasLowerCase2 = v2.name.exists(_.isLower)
            val notAnInt2 = v2.name.charAt(0).isLetter
            if (!hasLowerCase1 && notAnInt1 && !hasLowerCase2 && notAnInt2) {
              val s = Substitution(v1 -> v2)
              (List[Substitution](s) ++ firstMaps, true)
            } else {
              (List[Substitution](), true) //we have match, but it's not a variable to replace 
            }

          } else {
            (List[Substitution](), false)
          }
        }
        case _ => (List[Substitution](), false)
      }
    }

    case v1: Var => {
      f2 match {
        case v2: Var => {
          println("names: " + v1 + " and " + v2)

          //Something is going wrong here, when it probably should not be.
          val hasLowerCase1 = v1.name.exists(_.isLower)
          val notAnInt1 = v1.name.charAt(0).isLetter
          val hasLowerCase2 = v2.name.exists(_.isLower)
          val notAnInt2 = v2.name.charAt(0).isLetter
          if (!hasLowerCase1 && notAnInt1 && !hasLowerCase2 && notAnInt2) {
            val s = Substitution(v1 -> v2)
            (List[Substitution](s), true)
          } else {
            (List[Substitution](), true) //we have a match, but it's not a variable we want to replace?
          }

        }
        case _ => (List[Substitution](), false)
      }
    }

  }
}
