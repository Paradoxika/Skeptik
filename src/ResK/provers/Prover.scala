package ResK.provers

import ResK.proofs.Proof
import ResK.judgments.Judgment
//import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashSet => ISet}


object typeAliases {
  type Calculus[J <: Judgment, P <: Proof[J,P]] = Seq[InferenceRule[J, P]]
}

import typeAliases._

abstract class InferenceRule[J <: Judgment, P <: Proof[J,P]] {
  def apply(j: J): Seq[Seq[J]] // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(premises: Seq[P], conclusion: J): Option[P] // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  //def apply(premises: Seq[P]) : Seq[P] 
}

class SimpleProver[J <: Judgment, P <: Proof[J,P]](calculus: Calculus[J,P]) {
  // Simple generic bottom-up proof search
  def prove(goal:J) : Option[P] = {
    def proveRec(j: J, seen: ISet[J]): Option[P] = {
      val proofs = for (rule <- calculus.par; subGoals <- rule(j).par) yield {
        def proofOf(g: J) = if (seen contains g) None else proveRec(g, seen + j)
        val premises = subGoals.par.map(subGoal => proofOf(subGoal))
        if (premises.seq contains None) None 
        else {
          //println("goal: " + j)
          //println("premises")
          //premises.map(println(_))
          val p = rule(premises.map(_.get).seq, j)
          //println("proof: ")
          //println(p)
          p
        }
      }
      proofs.find(_.isInstanceOf[Some[P]]).getOrElse(None)
    }
    proveRec(goal, new ISet[J])
  }
    // Simple generic top-down proof search
    def prove(axioms: Seq[P], target: J): Option[P] = {
      None // ToDo
    }
  }

//class SimpleGridGainProver[J <: Judgment, P <: Proof[J,P]](calculus: Calculus[J,P]) {
//  // Simple generic bottom-up proof search
//  def prove(j: J): Option[P] = {
//    val proofs: Seq[Option[P]] = for (rule <- calculus; subGoals <- rule(j)) yield {
//      println()
//      println(j)
//      println(rule)
//      println(subGoals)
//      println()
//      val premises: Seq[Option[P]] = GridGainSeq(subGoals).map(subGoal => prove(subGoal))
////      val premises: Seq[Option[P]] = GridGainSeq(for (subGoal <- subGoals) yield (() => (new SimpleProver(calculus)).prove(subGoal))).map(p => p())
//      println("premises: " + premises)
//      if (premises contains None) {
//        println("premises do not contain None")
//        None 
//      }
//      else {
//        println("premises contain None")
//        rule(premises.map(_.get), j)
//      }
//    }
//    val proof = proofs.find(_.isInstanceOf[Some[P]]).getOrElse(None)
//    println()
//    println("return")
//    println(j)
//    println(proof)
//    println()
//    proof
//  }
//  
//  // Simple generic top-down proof search
//  def prove(axioms: Seq[P], target: J): Option[P] = {
//    None // ToDo
//  }
//}