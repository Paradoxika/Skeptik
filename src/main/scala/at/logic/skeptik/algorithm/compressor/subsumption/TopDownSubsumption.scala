package at.logic.skeptik.algorithm.compressor.subsumption

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}

/**
 * Version of top-down subsumption using the clause tree structure 
 * for storing nodes and searching for subsumers.
 */
abstract class TopDownSubsumption extends AbstractSubsumption {
  
  def apply(inputproof: Proof[N]) = {
    val proof = setTraverseOrder(inputproof)
    var clauseTree: ClauseTree = EmptyClauseTree()
    
    Proof(proof foldDown { ((node: N, fixedPremises: Seq[N]) => {
      //As described the clause tree class, the checkSubsumed method delivers a new clause Tree and a node, 
      //which is either subsuming the current one 
      //or is the current one itself, if no subsumer is stored in the clause tree
      val (newClauseTree,cltNode) = clauseTree.checkSubsumed(new NodeWithIterators(node))
      if (cltNode eq node) { //no subsumer was found in the clause tree
        val newNode = fixNode(node,fixedPremises)
        if (newNode eq node) { //Fixing did not result in a new node
          clauseTree = newClauseTree
          node
        }
        else { //the current node was fixed to a new node
          //This new node has to be inserted into the clause tree by checking for a subsumer
          val (newClauseTree2,cltNode2) = clauseTree.checkSubsumed(new NodeWithIterators(newNode))
          clauseTree = newClauseTree2
          //So far, I have not experienced any difference when replacing newNode with cltNode2 here.
          //This means that newNode never has a subsumer
          newNode
        }
      }
      else { //A subsumer was found and is returned. The clause tree is unchanged.
        cltNode
      }
      })
    })
  }
}

object TopDownSubsumption extends TopDownSubsumption with LeftRight

object TopDownSubsumptionRightLeft extends TopDownSubsumption with RightLeft
