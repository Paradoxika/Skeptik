package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.oldResolution._
import at.logic.skeptik.proof.oldResolution.defs._
import collection._

object ProofNodeFixing {
  def fix(p:ProofNode): ProofNode = {fix(List(p)); p}
  def fix(proofs:List[ProofNode]): List[ProofNode] = {
    val visitedProofNodes = new mutable.HashSet[ProofNode]
    val newRootsMap = new mutable.HashMap[ProofNode,ProofNode]
    for (p <- proofs) fixRec(p,visitedProofNodes,newRootsMap)
    for (p <- proofs) yield {newRootsMap(p)}
  }

  private def fixRec(proof:ProofNode, visitedProofNodes: mutable.HashSet[ProofNode], newRootsMap: mutable.HashMap[ProofNode,ProofNode]) : Unit = {
    if (!visitedProofNodes.contains(proof)) {
      visitedProofNodes += proof
      proof match {
        case i: Input => {
          if (i.children.length == 0) {
            newRootsMap += (i -> i)
          }
        }
        case n : Resolvent => {

          fixRec(n.left, visitedProofNodes,newRootsMap)
          fixRec(n.right, visitedProofNodes,newRootsMap)
          if (n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) {
            n.update
            if (n.children.length == 0) {
              newRootsMap += (n -> n)
            }
          }
          else {

            val survivingParent : ProofNode =
              if (n.left == deletedSubProofNode) n.right
              else if (n.right == deletedSubProofNode) n.left
              else if (n.left.clause.contains(n.pivot._1) && !n.right.clause.contains(n.pivot._2)) n.right
              else if (!n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) n.left
              else {
                if (length(n.left) < length(n.right)) n.left
                else n.right
              }

              if (n.children.length == 0) {
                newRootsMap += (n -> survivingParent)
              }

              survivingParent replaces n
              n.delete

          }
        }
      }
    }
  }
  
  def getInputNodes(roots: List[ProofNode]): Set[Input] = {
    val visitedProofNodes = new mutable.HashSet[ProofNode]
    val inputNodes = new mutable.HashSet[Input]
    def rec(p: ProofNode): Unit = {
      if (!visitedProofNodes.contains(p)) {
        visitedProofNodes += p
        p match {
          case i: Input => inputNodes += i
          case Resolvent(left, right) => {rec(left); rec(right)}
        }
      }
    }
    for (r <- roots) rec(r)
    inputNodes
  }


  def fixTopDown(proof: ProofNode):ProofNode = fixTopDown(List(proof)).head
  def fixTopDown(roots: List[ProofNode]): List[ProofNode] = {
    val oneParentVisited = new mutable.HashSet[ProofNode]
    val nodesToBeFixed = new mutable.Queue[ProofNode]
    val newRootsMap = new mutable.HashMap[ProofNode,ProofNode]

    val bothParentsVisited = new mutable.HashSet[ProofNode]

    val inputNodes = getInputNodes(roots)
    nodesToBeFixed ++= inputNodes
    oneParentVisited ++= inputNodes
    while (!nodesToBeFixed.isEmpty) fixNode(nodesToBeFixed.dequeue)

    def fixNode(p: ProofNode): Unit = {
      if (!oneParentVisited.contains(p)) {
        oneParentVisited += p
      }
      else if (!bothParentsVisited.contains(p)) {
        bothParentsVisited += p
        nodesToBeFixed ++= p.children
        p match {
          case i: Input => {
            if (i.children.length == 0) {
              newRootsMap += (i -> i)
            }
          }
          case r: Resolvent => {
            if (r.left.clause.contains(r.pivot._1) && r.right.clause.contains(r.pivot._2)) {
              r.update

              if (r.left.isInstanceOf[Resolvent] && r.left.children.forall(c => bothParentsVisited.contains(c))) r.left.asInstanceOf[Resolvent].forget
              if (r.right.isInstanceOf[Resolvent] && r.right.children.forall(c => bothParentsVisited.contains(c))) r.right.asInstanceOf[Resolvent].forget

              if (r.children.length == 0) {
                newRootsMap += (r -> r)
              }
            }
            else {
              val survivingParent : ProofNode =
                if (r.left == deletedSubProofNode) r.right
                else if (r.right == deletedSubProofNode) r.left
                else if (r.left.clause.contains(r.pivot._1) && !r.right.clause.contains(r.pivot._2)) r.right
                else if (!r.left.clause.contains(r.pivot._1) && r.right.clause.contains(r.pivot._2)) r.left
                else {
                  if (length(r.left) < length(r.right)) r.left
                  else r.right
                }

              if (r.children.length == 0) {
                newRootsMap += (r -> survivingParent)
              }
              survivingParent replaces r
              r.delete


            }
          }
        }
      }
      else {
        throw new Exception("Node is being called more than twice!")
      }
    }


    val result = (for (p <- roots) yield { newRootsMap(p) }).toList

    result
  }

}
