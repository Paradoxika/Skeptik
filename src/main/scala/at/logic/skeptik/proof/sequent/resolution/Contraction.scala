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

class Contraction(val premise: SequentProofNode, 
  val aux: E)(implicit unifiableVariables: MSet[Var])
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
   
  }
  
  
  def contract(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) ={
    //Want to do pair-wise comparison for formulas in the antecedent of the premise
    val ant = premise.conclusion.ant
    
    //TODO: this 
    
    //Check a pair:
    contractPair(ant.head, ant.last)
  }
  
  def contractPair(f1: E, f2: E): (List[Substitution], Boolean) = f1 match {
      case App(e1, e2) => {
        f2 match { 
          case App(e3, e4) => {
        	
            val (firstMaps, firstBool) = contractPair(e1, e3)
            if(firstBool) {
              val (secondMaps, secondBool) = contractPair(e2, e4)
              if(secondBool){
                (firstMaps ++ secondMaps, true)
              } else {
                (List[Substitution](), false)  
              }
            } else {
              (List[Substitution](), false)
            }
          }
          case _ => (List[Substitution](), false)
        } 
      }
      case Abs(v1,e1) => {
        f2 match {
          case Abs(v2,e2) => {
            val (firstMaps, firstBool) = contractPair(e1, e2)
            if(firstBool){
              val s = Substitution(v1 -> v2)
              (List[Substitution](s) ++ firstMaps, true)
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
            val s = Substitution(v1 -> v2)
            (List[Substitution](s), true)
          }
          case _ => (List[Substitution](), false)
        }
      } 
      
  }
}
