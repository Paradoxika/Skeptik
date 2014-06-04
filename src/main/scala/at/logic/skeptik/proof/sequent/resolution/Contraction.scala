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

class Contraction(val premise: SequentProofNode, val newAnt: Seq[E])(implicit unifiableVariables: MSet[Var])
  extends SequentProofNode with Unary
  with NoMainFormula {

  //TODO: define this?
  def auxFormulas = ???

  override val conclusionContext = {
    val antecedent = newAnt
    val succedent = premise.conclusion.suc
    new Sequent(antecedent, succedent)
  }
}

object Contraction {
  def apply(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {
    //println(contract(premise)(unifiableVariables))
    new Contraction(premise, contract(premise)(unifiableVariables)) 
  }

  def contract(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): Seq[E] = {
    //Want to do pair-wise comparison for formulas in the antecedent of the premise
    val ant = premise.conclusion.ant

    var first = 0
    var second = 0
    
    var change = null.asInstanceOf[List[Substitution]]

    //Check if the current head matches the rest of the antecedent
    def checkHead(h: E, t: Seq[E], start: Int): (Boolean, Int) = {
      if (t.length == 0) {
        return (false, -1)
      } else {
        second += 1
        val (replacements, matched) = contractPair(h, t.head)
        println("replacements: " + replacements)
        if (matched) {
          change = replacements
          (true, start)
        } else {
          checkHead(h, t.tail, start+1)
        }
      }
    }

    def checkAllPairs(ant: Seq[E], start: Int): (Boolean, Int, Int) = {
      println("in checkAllPairs")
      if (ant.length == 0) {
        return (false, -1, -1)
      }
      val h = ant.head
      //If the head did not match anything else, check the rest
      val result = checkHead(h, ant.tail, start+1)
      if (!result._1) {
        checkAllPairs(ant.tail, start+1)

        //if it did, we found a match, return true.
      } else {
        return (true, start,result._2)
      }
    }
    
    val temp = checkAllPairs(ant,0)
    
    println("removing " + temp._2 + " and " + temp._3)
    def removeNth(ant: Seq[E], n: Int, step: Int) : List[E] = {
      if(n == step){
        (ant.tail).toList
      } else {
        List(ant.head) ++ removeNth(ant.tail, n, step+1)
      }
    }    

    if(temp._3 != -1){
      removeNth(premise.conclusion.ant, temp._3, 0).toSeq
    } else {
      premise.conclusion.ant
    }

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
              (List[Substitution](), v1.name.equals(v2.name)) //we might have match, but it's not a variable to replace 
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
          //Something is going wrong here, when it probably should not be.
          val hasLowerCase1 = v1.name.exists(_.isLower)
          val notAnInt1 = v1.name.charAt(0).isLetter
          val hasLowerCase2 = v2.name.exists(_.isLower)
          val notAnInt2 = v2.name.charAt(0).isLetter
          if (!hasLowerCase1 && notAnInt1 && !hasLowerCase2 && notAnInt2) {
            val s = Substitution(v1 -> v2)
            (List[Substitution](s), true)
          } else {
            (List[Substitution](), v1.name.equals(v2.name)) //we might have a match, but it's not a variable we want to replace?
          }

        }
        case _ => (List[Substitution](), false)
      }
    }

  }
}
