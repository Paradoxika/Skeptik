package at.logic.skeptik.algorithm.compressor.split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.{Axiom,R}
import at.logic.skeptik.expression.E
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.algorithm.compressor._

/**
 * Recursive Split algorithm recursively applies the split algorithm to the roots premises of the result of an application of split, before resolving those premises to obtain the new root node.
 * As opposed to an iterative application of split, this has the result that the first chosen variable ends up the lowest pivot and does not move up as split is called iteratively.
 * Also different variables can be chosen in the different subtrees.
 * 
 * The recursive calls can be stopped either after some timeout or a desired recursion depth has been reached.
 */
abstract class RecursiveSplit
extends Split with AbstractSplitHeuristic {

  var start:Long = 0.toLong
  
  /**
   * Defines which split algorithm is applied recursively
   */
  def splitOnce(proof: Proof[N]):Proof[N]
  
  /**
   * Defines what algorithm is run after recursively splitting.
   * This needs to be done since subtrees can compute the same node and therefore create unnecessary decompression.
   * Therefore a reasonable choice here DAGify, but top-down subsumption might also be good.
   */
  def postProcessingAlgorithm:(Proof[N] => Proof[N])
  
  /**This method starts the recursion once and applies the post processing algorithm afterwards.
   * Only positively compressed proofs are accepted, negative compressions are discarded.
   * minimal maxDepth is 1, because checking the stopCriteria before splitting might lead to one branch being split, while the other is not and they end up not fitting together.
   */
  override def applyOnce(proof: Proof[N]):Proof[N] = {
    start = System.nanoTime()
    val compproof = postProcessingAlgorithm(applyRecursively(proof,1,false))
    if (!(compproof.root.conclusion.size == 1)) println("not the empty root!")
    if (compproof.size < proof.size) compproof else proof
  }
  
  /** 
   *  Criteria when the recursion should stop.
   *  Can either be a timeout of a recursion depth.
   *  Returns true if the criteria is met, false otherwise.
   */
  def stopCriteria(recursionDepth: Int): Boolean
  
  /**
   * Recursive split method
   * Keeps track of the recursion depth.
   * Splitting can be prohibited, if the third parameter is set to false.
   * Prohibiting splitting is useful, if one of the branches to split upon is an axiom or an unchecked inference.
   * In such a case, the other branch can still be recursively split, but this branch itself should not be split to keep a valid proof (since the root will be changed and might not be resolvable to the other branches root).
   */
  def applyRecursively(proof: Proof[N], recursionDepth: Int, noSplit: Boolean):Proof[N] = {
    val splitProof = if (noSplit) proof 
    else {
      splitOnce(proof)
    }
    splitProof.root match {
      case R(left,right,pivot,_) => {
        //The stopping criteria has to be checked here and not further before splitting this proof, because either both branches have to be split or none.
        if (stopCriteria(recursionDepth)) splitProof
        else {
          //Only if both branches are resolvents split should be called on them
          //If one is not a leaf node, then split prohibited for the other branch
          val applied = (left,right) match {
            //The .par method allows for parallel recursive splitting
            case (R(_,_,_,_),R(_,_,_,_)) => List(left,right).par.map(subProof => applyRecursively(subProof, recursionDepth + 1,false).root)
            case (R(_,_,_,_),_) => List(applyRecursively(left, recursionDepth + 1,true).root,right)
            case (_,R(_,_,_,_)) => List(left,applyRecursively(right, recursionDepth + 1,true).root)
            case _ => List(left,right)
          }
          Proof(R(applied.head,applied.last,pivot,true))
        }
      }
      //At leafs one cannot split recursively anymore and the subproof is returned
      case _ => splitProof
    }
  }
}



/**
 * Split once like Boudou split, i.e. try variables until one shows positive compression
 */
trait splitOnceBoudou 
extends Split with AbstractSplitHeuristic {
  def splitOnce(proof: Proof[N]):Proof[N] = {
    val (measures, measureSum) = computeMeasures(proof)
    def repeat(sum: Long):Proof[N] = {
      val selectedVariable = chooseVariable(measures, sum)
      val (left, right) = split(proof, selectedVariable)
      val compressedProof: Proof[N] = R(left, right, selectedVariable)
      if (compressedProof.size < proof.size) compressedProof
      else {
        val newSum = sum - measures(selectedVariable)
        if (newSum < 1) proof else {
          measures.remove(selectedVariable)
          repeat(newSum)
        }
      }
    }
    repeat(measureSum)
  }
}

/**
 * Split once and accept only positively compressed proofs
 */
trait splitOnceSimple
extends Split with AbstractSplitHeuristic {
  def splitOnce(proof: Proof[N]):Proof[N] = {
    val selectedVariable = selectVariable(proof)
    val (left, right) = split(proof, selectedVariable)
    val compressedProof: Proof[N] = R(left, right, selectedVariable)
    if (compressedProof.size < proof.size) compressedProof else proof
  }
}

/**
 * Stopping criteria is a given depth
 */
trait depthStop {
  def maxDepth: Int
  def stopCriteria(recursionDepth:Int): Boolean = {
    recursionDepth >= maxDepth
  }
}

/**
 * Stopping criteria is a given timeout
 * Note that this is a sort of inner timeout.
 * If the trait Timeout is used for a splitter, then the recursive split method is called until the outer timeout is reached.
 * One call of recursive split will be cancelled after the inner timeout has been reached.
 */
trait timeStop {
  def start: Long
  def recursionTimeout: Int
  def stopCriteria(recursionDepth:Int): Boolean = {
    ((System.nanoTime() - start)/1000000 > recursionTimeout)
  }
}

/**
 * Post processing algorithm is DAGify
 */
trait dag {
  def postProcessingAlgorithm:(Proof[N] => Proof[N]) = DAGify
}

/**
 * Post processing algorithm is top-down subsumption
 */
trait tds {
  def postProcessingAlgorithm:(Proof[N] => Proof[N]) = TopDownLeftRightSubsumption
}

/**
 * The recursive split algorithm should applied only once and not until a timeout is reached
 */
trait outTimeout {
  def applyOnce(p: Proof[N]): Proof[N]
  def apply(p: Proof[N]): Proof[N] = {
    applyOnce(p)
  }
}

/**
 * Actual recursive splitters.
 * There are many combinations how to select the traits for stopping criteria, splitting once, post processing algorithms and timouts.
 * I have not yet found out which one is the most fruitful combination.
 */
class DetADRecSplitTime(val recursionTimeout: Int, val timeout: Int)
extends RecursiveSplit with AdditivityHeuristic with DeterministicChoice with timeStop with dag with Timeout with splitOnceSimple

class RSTDS(val recursionTimeout: Int, val timeout: Int)
extends RecursiveSplit with AdditivityHeuristic with DeterministicChoice with timeStop with tds with Timeout with splitOnceSimple

class RSTDSNT(val maxDepth: Int)
extends RecursiveSplit with AdditivityHeuristic with DeterministicChoice with depthStop with tds with outTimeout with splitOnceSimple

class DepthTimeRS(val maxDepth: Int,val timeout: Int)
extends RecursiveSplit with AdditivityHeuristic with DeterministicChoice with depthStop with dag with Timeout with splitOnceSimple