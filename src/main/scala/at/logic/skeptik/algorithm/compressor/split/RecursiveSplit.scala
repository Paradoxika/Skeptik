package at.logic.skeptik.algorithm.compressor.split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.{Axiom,R}
import at.logic.skeptik.expression.E
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.algorithm.compressor.DAGify

abstract class RecursiveSplit
extends Split with AbstractSplitHeuristic {

  val tabus = MMap[Proof[N],List[E]]()
  var start:Long = 0.toLong
  
  def splitOnce(p: Proof[N]): Proof[N] = {
    val selectedVariable = selectVariable(p,tabus.getOrElse(p, List[E]()))
    val (left, right) = split(p, selectedVariable)
    val compressedProof: Proof[N] = R(left, right, selectedVariable)
    if (compressedProof.size < p.size) {
      compressedProof
    }
    else {
      tabus.update(p, selectedVariable::tabus.getOrElse(p, List[E]()))
      p
    }
  }
  
  //minimal maxDepth is 1, because checking the stopCriteria before splitting might lead to one branch being split, while the other is not and they end up not fitting together
  def apply(proof: Proof[N]):Proof[N] = {
    start = System.nanoTime()
    val compproof = DAGify(applyRecursively(proof,1,false))
    if (!(compproof.root.conclusion.size == 1)) println("not the empty root!")
    compproof
  }
  
  def stopCriteria(recursionDepth: Int): Boolean
  
  def applyRecursively(proof: Proof[N], recursionDepth: Int, noSplit: Boolean):Proof[N] = {
//    println("apply once to " + proof.root)
    val splitProof = if (noSplit) proof else applyOnce(proof)
    splitProof.root match {
      case R(left,right,pivot,_) => {
        if (stopCriteria(recursionDepth)) splitProof
        else {
          val applied = (left,right) match {
            case (R(_,_,_,_),R(_,_,_,_)) => List(left,right).par.map(subProof => applyRecursively(subProof, recursionDepth + 1,false).root)
            case (R(_,_,_,_),_) => List(applyRecursively(left, recursionDepth + 1,true).root,right)
            case (_,R(_,_,_,_)) => List(left,applyRecursively(right, recursionDepth + 1,true).root)
            case _ => List(left,right)
          }
//          println(left.getClass() + " ~ " + right.getClass())
//          println(applied.head.getClass() + " ~ " + applied.last.getClass())
//          println("left before: " + left + " left after: " + applied.head)
//          println("right before: " + right + " right after: " + applied.last)
          Proof(R(applied.head,applied.last,pivot,true))
        }
      }
      case _ => splitProof
    }
  }
}

class DetADRecSplitTime(val recursionTimeout: Int)
extends RecursiveSplit with AdditivityHeuristic with DeterministicChoice with timeStop

class DetADRecSplitDepth(val maxDepth: Int)
extends RecursiveSplit with AdditivityHeuristic with DeterministicChoice with depthStop

trait depthStop {
  def maxDepth: Int
  def stopCriteria(recursionDepth:Int): Boolean = {
    recursionDepth >= maxDepth
  }
}

trait timeStop {
  def start: Long
  def recursionTimeout: Int
  def stopCriteria(recursionDepth:Int): Boolean = {
    ((System.nanoTime() - start)/1000000 > recursionTimeout)
  }
}