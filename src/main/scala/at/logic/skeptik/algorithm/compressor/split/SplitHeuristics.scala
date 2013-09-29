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

/**
 * Heuristic for selecting split variable.
 * Computes some measure for each node, where the higher measure should represent a better variable.
 * The sum of the measures is also computed to select variables more efficient.
 * The variables can either be selected deterministically or randomly.
 */
trait AbstractSplitHeuristic extends Split {
  def computeMeasures(proof: Proof[N]): (MMap[E,Long],Long)
  
  def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long): E
  
  def selectVariable(proof: Proof[N]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    chooseVariable(measureMap, measureSum)
  }
}

/**
 * The additivity heuristic is the original heuristic proposed by Scott Cotton.
 * It measures how much a clause grows after resolving, using the variable as pivot, 
 * in comparison to its biggest premise.
 */
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

/**
 * The weighted depth heuristic modifies the additivity heuristic, 
 * by multiplying the additivity with the depth of the node.
 * 
 * The depth of a node is defined here as the maximum path length from the root to the node.
 * Therefore pivot used at nodes with a higher depth have a higher chance of being selected.
 */
trait WeightedDepthHeuristic
extends AbstractSplitHeuristic {
  def computeMeasures(proof: Proof[N]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[E,Long]()
    def visit(node: N, children:Seq[Int]): Int = {
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

/**
 * The remove irregularities heuristic modifies the additivity heuristic, 
 * by multiplying the additivity by the number of times the pivot was used already in this path.
 * 
 * If a variable occurs two or more times as a pivot in a resolution path, it is called irregular.
 * Therefore irregular pivots are likely to be removed using this heuristic.
 * Removing irregularities might lead to exponential proof growth.
 */
trait RemoveIrregularityHeuristic
extends AbstractSplitHeuristic {
  def computeMeasures(proof: Proof[N]) = {
    val repetition = MMap[E,Long]()
    var totalRepetition = 0.toLong
    def visit(node: N, children: Seq[Map[E,Long]]): Map[E,Long] = node match {
      case R(_,_,aux,_) => {
        val tmp = (Map(aux -> 1.toLong) /: children) ((A,B) => A |+| B)
        val rep = (((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1) * tmp(aux)
        totalRepetition += rep
        repetition.update(aux, repetition.getOrElse(aux, 0.toLong) + rep)
        tmp
      }
      case _ => (children foldLeft Map[E,Long]()) ((A,B) => A |+| B)
    }
    proof bottomUp visit
    (repetition,totalRepetition)
  }
}

/**
 * The leave irregularities heuristic is the counterpart to the remove irregularities heuristic.
 * 
 * It only adds the additivity to the variable, 
 * if the variable was not used before as pivot in the resolution path.
 * Therefore irregular variables will end up having a smaller measure.
 */
trait LeaveIrregularitiesHeuristic
extends AbstractSplitHeuristic {
  def computeMeasures(proof: Proof[N]) = {
    val repetition = MMap[E,Long]()
    var totalRepetition = 0.toLong
    def visit(node: N, children: Seq[ISet[E]]):ISet[E] = {
      val fromChildren = (ISet[E]() /: children) ((A,B) => A union B)
      node match {
        case R(_,_,aux,_) => {
          val add = if (fromChildren.contains(aux)) 0.toLong else (((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1)
          totalRepetition += add
          repetition.update(aux, repetition.getOrElse(aux, 0.toLong) + add)
          fromChildren + aux
        }
        case _ => fromChildren
      }
    }
    proof bottomUp visit
    (repetition,totalRepetition)
  }
}

/**
 * The sequent size heuristic adds the size of the conclusion sequent to the variable measure, 
 * wherever it is used as a pivot.
 */
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
