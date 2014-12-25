package at.logic.skeptik.algorithm.compressor.subsumption

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashSet => MSet}
import scala.collection.immutable.{HashSet => ISet}

/**
 * Naive bottom-up subsumption.
 * 
 * Bottom-up subsumption uses two traversals.
 * The first, in a bottom-up fashion, searches for subsuming nodes
 * among all the nodes that have been visited earlier. 
 * The second, in a top-down fashion, fixes the proof and replaces nodes
 * according to the replacements collected in the first traversal.
 * 
 * There is still a problem with how these two traversals work in combination.
 * The order for a top-down traversal is not preserved when applying replacements,
 * that were found in a bottom-up fashion.
 * This has several negative effects. 
 * For example one replacement might be good (subsuming + not ancestor) before another replacement is applied, 
 * but the ancestor condition might be violated afterwards.
 * Also some nodes might be get fixed, but get new ancestors later, 
 * because of the application of some replacement applied after visiting the node.
 * Therefore the previously fixed node should be fixed again.
 * Solving this issue is not trivial. 
 * A mutable proof structure might help. 
 * A jumping version of proof traversal does not resolve the issue.
 * 
 * There is no version of bottom-up subsumption yet that uses the clause tree structure.
 * This is because while checking subsumption, the ancestor check is not done in the clause tree.
 * The clause tree structure probably has to be extended to be able to do additional checks 
 * while searching for a subsuming clause.
 */
abstract class BottomUpSubsumption extends AbstractSubsumption {
  //Abstract method checking if one node is an ancestor of another node
  //true if the second argument is not an ancestor of the first argument
  def notAncestor(node: N, ancestor: N):Boolean
  def apply(inputproof: Proof[N]) = {
    
    //Map for replacements that have been collected in the bottom-up traversal
    val replaceNodes = new MMap[N,N]
    
    //Set of nodes that have been visited
    val nodeSet = new MSet[N]
    
    def collect(node: N, results: Seq[Unit]):Unit = {
      val subsumed = nodeSet.find( A => (A.conclusion subsequentOf node.conclusion) && (notAncestor(A,node)))
      subsumed match {
        //No replacement has been found and therefore the node is added to the set of visited nodes
        case None => nodeSet += node
        //A replacement is found and stored in the map
        //The original node is not stored in the node-set, 
        //because it is not desirable to replace another node by a replaced node
        case Some(u) => {
          replaceNodes(node) = u
        }
      }
    }
    val proof = setTraverseOrder(inputproof)

    proof bottomUp collect
    
    /** Replaces or fixes the nodes in a top-down traversal */
    Proof(proof foldDown { ((node: N, fixedPremises: Seq[N]) => {
      replaceNodes.getOrElse(node,{fixNode(node,fixedPremises)})
    })})
  }
}

/**
 * Version of bottom-up subsumption, which favours computation speed over memory consumption.
 * 
 * This version keeps track of the ancestor nodes of every node in form of maps 
 * with nodes as keys and sets of nodes as values.
 * 
 * Whenever the notAncestor method is called, 
 * the ancestors are either computed or read if they have already been computed. 
 * It is then checked if the node of interest is contained in the resulting set.
 */
abstract class BottomUpSubsumptionTime extends BottomUpSubsumption {
  val ancestors = new MMap[N,ISet[N]]
  def notAncestor(node: N, ancestor: N):Boolean = {
    !(ancestors.getOrElse(node, {Proof(node) foldDown collectAncestors; ancestors(node)}) contains ancestor)
  }
  
  /** Computes the ancestors of a node as a union of all ancestors of the premises plus the node itself */
  def collectAncestors(node: N, premises: Seq[N]):N = {
    ancestors(node) = (ISet(node) /: premises){ (l1,l2) =>
      l1 union ancestors(l2)
    }
    node
  }
}

object BottomUpSubsumptionTime extends BottomUpSubsumptionTime with LeftRight
object BottomUpSubsumptionTimeRightLeft extends BottomUpSubsumptionTime with RightLeft

/**
 * Version of bottom-up subsumption, which does not need so much memory, but takes more time.
 * 
 * The ancestor check is done by comparing all ancestors of the first argument to the second argument.
 * This is done in such a way, that no comparisons are done twice and the comparison stops
 * as soon as the second argument is equal to an ancestor.
 */
abstract class BottomUpSubsumptionMemory extends BottomUpSubsumption {
  def notAncestor(node: N, ancestor: N):Boolean = {
    !(node existsAmongAncestors {_ eq ancestor})
  }
}

object BottomUpSubsumptionMemory extends BottomUpSubsumptionMemory with LeftRight
object BottomUpSubsumptionMemoryRightLeft extends BottomUpSubsumptionMemory with RightLeft