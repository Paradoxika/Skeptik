package skeptik.algorithms

import skeptik.proofs.oldResolution.resolution._
import skeptik.proofs.oldResolution.resolution.measures._
import scala.collection._

object ProofFixing {
  def fix(p:Proof): Proof = {fix(List(p)); p}
  def fix(proofs:List[Proof]): List[Proof] = {
    val visitedProofs = new mutable.HashSet[Proof]
    val newRootsMap = new mutable.HashMap[Proof,Proof]
    for (p <- proofs) fixRec(p,visitedProofs,newRootsMap)
    for (p <- proofs) yield {newRootsMap(p)}
  }

  private def fixRec(proof:Proof, visitedProofs: mutable.HashSet[Proof], newRootsMap: mutable.HashMap[Proof,Proof]) : Unit = {
    if (!visitedProofs.contains(proof)) {
      visitedProofs += proof
      proof match {
        case i: Input => {
          if (i.children.length == 0) {
            newRootsMap += (i -> i)
          }
        }
        case n : Resolvent => {

          fixRec(n.left, visitedProofs,newRootsMap)
          fixRec(n.right, visitedProofs,newRootsMap)
          if (n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) {
            n.update
            if (n.children.length == 0) {
              newRootsMap += (n -> n)
            }
          }
          else {

            val survivingParent : Proof =
              if (n.left == deletedSubProof) n.right
              else if (n.right == deletedSubProof) n.left
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
  
  def getInputNodes(roots: List[Proof]): Set[Input] = {
    val visitedProofs = new mutable.HashSet[Proof]
    val inputNodes = new mutable.HashSet[Input]
    def rec(p: Proof): Unit = {
      if (!visitedProofs.contains(p)) {
        visitedProofs += p
        p match {
          case i: Input => inputNodes += i
          case Resolvent(left, right) => {rec(left); rec(right)}
        }
      }
    }
    for (r <- roots) rec(r)
    inputNodes
  }


  def fixTopDown(proof: Proof):Proof = fixTopDown(List(proof)).head
  def fixTopDown(roots: List[Proof]): List[Proof] = {
    val oneParentVisited = new mutable.HashSet[Proof]
    val nodesToBeFixed = new mutable.Queue[Proof]
    val newRootsMap = new mutable.HashMap[Proof,Proof]

    val bothParentsVisited = new mutable.HashSet[Proof]

    val inputNodes = getInputNodes(roots)
    nodesToBeFixed ++= inputNodes
    oneParentVisited ++= inputNodes
    while (!nodesToBeFixed.isEmpty) fixNode(nodesToBeFixed.dequeue)

    def fixNode(p: Proof): Unit = {
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
              val survivingParent : Proof =
                if (r.left == deletedSubProof) r.right
                else if (r.right == deletedSubProof) r.left
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
