/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ResK.algorithms

import ResK.calculi.resolution._
import ResK.calculi.resolution.measures._
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
            //println("newRoot Input: " + i.id)
            newRootsMap += (i -> i)
          }
        }
        case n : Resolvent => {

          fixRec(n.left, visitedProofs,newRootsMap)
          fixRec(n.right, visitedProofs,newRootsMap)
          if (n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) {
            n.update
            if (n.children.length == 0) {
              //println("newRoot Resolvent: " + n.id)
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
                //println("newRoot Surviving Parent: " + n.id + " " + survivingParent.id)
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
    //println("inputNodes length: " + inputNodes.size)
    inputNodes
  }


  def fixTopDown(proof: Proof):Proof = fixTopDown(List(proof)).head
  def fixTopDown(roots: List[Proof]): List[Proof] = {
    val oneParentVisited = new mutable.HashSet[Proof]
    val nodesToBeFixed = new mutable.Queue[Proof]
    val newRootsMap = new mutable.HashMap[Proof,Proof]

    val bothParentsVisited = new mutable.HashSet[Proof]

//    val hasOtherParentVisited = new mutable.HashSet[Proof]

    val inputNodes = getInputNodes(roots)
    nodesToBeFixed ++= inputNodes
    oneParentVisited ++= inputNodes
    while (!nodesToBeFixed.isEmpty) fixNode(nodesToBeFixed.dequeue)


       //println(roots.length)
    //println(roots.map(n => n.id + ": " + n.clause))
    //println(inputs.length)
    def fixNode(p: Proof): Unit = {
      //println("fixing node: " + p.id)
      //println(p.children.length)
      //println(p.children.map(c => c.id))
      if (!oneParentVisited.contains(p)) {
        //println("oneParentVisited: " + p.id)
        oneParentVisited += p
      }
      else if (!bothParentsVisited.contains(p)) {
        //println("bothParentsVisited: " + p.id)
        bothParentsVisited += p
        nodesToBeFixed ++= p.children
        p match {
          case i: Input => {
            if (i.children.length == 0) {
              //println("newRoot Input: " + i.id)
              newRootsMap += (i -> i)
            }
          }
          case r: Resolvent => {
            if (r.left.clause.contains(r.pivot._1) && r.right.clause.contains(r.pivot._2)) {
              //println("standard case")
              r.update
//
              if (r.left.isInstanceOf[Resolvent] && r.left.children.forall(c => bothParentsVisited.contains(c))) r.left.asInstanceOf[Resolvent].forget
              if (r.right.isInstanceOf[Resolvent] && r.right.children.forall(c => bothParentsVisited.contains(c))) r.right.asInstanceOf[Resolvent].forget

              if (r.children.length == 0) {
                //println("newRoot Resolvent: " + r.id)
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


    val result = (for (p <- roots) yield { newRootsMap(p)
      //println(p.id)
//      if (newRootsMap.contains(p)) newRootsMap(p)
//      else {
//        println("not found in newRootsMap: " + p.id)
//        null
//      }
    }).toList
    //println(result.length)
    //println(result)
    result
  }


 


//  def fixTopDown(proof: Proof):Proof = fixTopDown(List(proof)).head
//  def fixTopDown(roots: List[Proof]): List[Proof] = {
//    val oneParentVisited = new mutable.HashSet[Proof]
//    val inputs = getInputNodes(roots)
//    val newRootsMap = new mutable.HashMap[Proof,Proof]
//    println(roots.length)
//    println(roots.map(n => n.id + ": " + n.clause))
//    println(inputs.length)
//    def rec(p: Proof): Unit = {
//      println("fixing node: " + p.id)
//      println(p.children.length)
//      println(p.children.map(c => c.id))
//      p match {
//        case i: Input => {
//          oneParentVisited += i
//          if (i.children.length == 0) {
//            println("newRoot Input: " + i.id)
//            newRootsMap += (i -> i)
//          }
//          else for (c <- i.children) rec(c)
//        }
//        case r: Resolvent => {
//          if (oneParentVisited.contains(r.left) && fixedProofs.contains(r.right)) {
//            println("left clause: " + r.left.id + " " + r.left.clause)
//            println("right clause: " + r.right.id + " " + r.right.clause)
//            println(r.pivot)
//            if (r.left.clause.contains(r.pivot._1) && r.right.clause.contains(r.pivot._2)) {
//              println("standard case")
//              r.update
//              oneParentVisited += r
//
//              if (r.left.isInstanceOf[Resolvent] && r.left.children.forall(c => oneParentVisited.contains(c))) r.left.asInstanceOf[Resolvent].forget
//              if (r.right.isInstanceOf[Resolvent] && r.right.children.forall(c => oneParentVisited.contains(c))) r.right.asInstanceOf[Resolvent].forget
//
//              if (r.children.length == 0) {
//                println("newRoot Resolvent: " + r.id)
//                newRootsMap += (r -> r)
//              }
//              else for (c <- r.children) rec(c)
//            }
//            else {
//              println("other case")
//              val survivingParent : Proof =
//                if (r.left == deletedSubProof) r.right
//                else if (r.right == deletedSubProof) r.left
//                else if (r.left.clause.contains(r.pivot._1) && !r.right.clause.contains(r.pivot._2)) {println("left contains. right doesn't.");r.right}
//                else if (!r.left.clause.contains(r.pivot._1) && r.right.clause.contains(r.pivot._2)) r.left
//                else {
//                  println("here")
//                  if (r.left.length < r.right.length) r.left
//                  else r.right
//                }
//              r.left.children -= r
//              r.right.children -= r
//              if (r.children.length == 0) {
//                println("newRoot Surviving Parent: " + r.id + " " + survivingParent.id)
//                newRootsMap += (r -> survivingParent)
//              }
//              else {
//                for (child <- r.children) {
//                  if (child.left == r) child.left = survivingParent
//                  else child.right = survivingParent
//                  survivingParent.children = child::survivingParent.children
//                }
//                println("CHILDREN: " + r.children.length )
//                val newChildrenOfSurvivingParent = r.children.toList
//                println("CHILDREN: " + newChildrenOfSurvivingParent.length )
//                r.children = Nil
//                r.left = null
//                r.right = null
//                println("CHILDREN: " + newChildrenOfSurvivingParent.length )
//                for (c <- newChildrenOfSurvivingParent) {
//                  rec(c)
//                }
//              }
//            }
//          }
//        }
//      }
//    }
//    for (i <- inputs) rec(i)
//    println(newRootsMap.size)
//    for ((p1,p2) <- newRootsMap) println(p1.id + " : " + p2.id)
//    val result = (for (p <- roots) yield {
//      if (newRootsMap.contains(p)) newRootsMap(p)
//      else {
//        println("not found in newRootsMap: " + p.id)
//        null
//      }
//    }).toList
//    println(result.length)
//    result
//  }

}
