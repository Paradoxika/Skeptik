package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.expression.E
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}
import scala.collection.immutable.{HashSet => ISet}
import org.specs2.internal.scalaz._
import Scalaz._

trait AbstractSplitHeuristic extends Split {
  def computeMeasures(proof: Proof[N]):(MMap[E,Long],Long)
  
  def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long):E
  
  def selectVariable(proof: Proof[N], tabu: List[E]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    val reducedMap = measureMap -- tabu
    var reducedSum = measureSum
    tabu.foreach(t => if (measureMap.isDefinedAt(t)) reducedSum = reducedSum - measureMap(t))
//    if (reducedMap.isEmpty) tabu.head
//    else 
      chooseVariable(reducedMap,reducedSum)
  }
  
  def selectVariable(proof: Proof[N]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
//    println("total measure.: " + measureSum)
//    println("literal measurements:")
//    measureMap.foreach(A => println(A._1 + " -> " + A._2))
    chooseVariable(measureMap, measureSum)
  }
}

trait AdditivityHeuristic
extends AbstractSplitHeuristic  {
  def computeMeasures(proof: Proof[N]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[E,Long]()
    def visit(node: N) = node match {
      case R(_,_,aux,_) =>
        val nodeAdditivity = ((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1
        totalAdditivity += nodeAdditivity
        literalAdditivity.update(aux, literalAdditivity.getOrElse(aux,0.toLong) + nodeAdditivity)
      case _ =>
    }
    proof.foreach(visit)
    (literalAdditivity, totalAdditivity)
  }
}

trait WeightedDepthHeuristic
extends AbstractSplitHeuristic {
  def computeMeasures(proof: Proof[N]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[E,Long]()
    def visit(node: N, children:Seq[Int]):Int = {
      val depth = if (children.size > 0) children.min + 1 else 0
      node match {
        case R(_,_,aux,_) =>
          val nodeAdditivity = (((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1) * depth
          totalAdditivity += nodeAdditivity
          literalAdditivity.update(aux, literalAdditivity.getOrElse(aux,0.toLong) + nodeAdditivity)
        case _ => 
      }
      depth
    }
    proof bottomUp visit
    (literalAdditivity, totalAdditivity)
  }
}

trait PunishIrregularityHeuristic
extends AbstractSplitHeuristic {
  def computeMeasures(proof: Proof[N]) = {
    val repetition = MMap[E,Long]()
    var totalRepetition = 0.toLong
    def visit(node: N, children: Seq[Map[E,Long]]):Map[E,Long] = {
      node match {
        case R(_,_,aux,_) => {
          val tmp = (Map(aux -> 1.toLong) /: children) ((A,B) => A |+| B)
//          val rep = (tmp(aux)-1)*(tmp(aux)-1)
          val rep = (((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1) * tmp(aux)
//          val rep = tmp(aux)
//          if (rep > 0) {
            totalRepetition += rep
            repetition.update(aux, repetition.getOrElse(aux, 0.toLong) + rep)
//          }
          tmp
        }
        case _ => (Map[E,Long]() /: children) ((A,B) => A |+| B)
      }
    }
    proof bottomUp visit
    (repetition,totalRepetition)
  }
}

trait LeaveIrregularitiesHeuristic
extends AbstractSplitHeuristic {
  def computeMeasures(proof: Proof[N]) = {
    val repetition = MMap[E,Long]()
    var totalRepetition = 0.toLong
    def visit(node: N, children: Seq[ISet[E]]):ISet[E] = {
      val fromChildren = (ISet[E]() /: children) ((A,B) => A union B)
      node match {
        case R(_,_,aux,_) => {
//          val rep = (tmp(aux)-1)*(tmp(aux)-1)
          val add = if (fromChildren.contains(aux)) 0.toLong else (((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1)
//          val rep = tmp(aux)
//          if (rep > 0) {
            totalRepetition += add
            repetition.update(aux, repetition.getOrElse(aux, 0.toLong) + add)
//          }
          fromChildren + aux
        }
        case _ => fromChildren
      }
    }
    proof bottomUp visit
    (repetition,totalRepetition)
  }
}

trait SequentSizeHeuristic
extends AbstractSplitHeuristic  {
  def computeMeasures(proof: Proof[N]) = {
    var totalSize = 0.toLong
    val literalSize = MMap[E,Long]()
    def visit(node: N) = node match {
      case R(_,_,aux,_) =>
        val currSize = (node.premises(0).conclusion.size + node.premises(1).conclusion.size).toLong
        totalSize += currSize
        literalSize.update(aux, literalSize.getOrElse(aux,0.toLong) + currSize)
      case _ =>
    }
    proof.foreach(visit)
    (literalSize, totalSize)
  }
}
