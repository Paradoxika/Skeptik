/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import proofCompression.Utilities._
import scala.collection.mutable._

object ProofRegularization {
  val deletedSubProof = Input(L("DELETED",true)::Nil)

//  def isRegular(proof: ResolutionProof) = {
//    def isRegularRec(p: ResolutionProof, pivotsAbove: HashSet[Atom], visitedProofs: HashMap[ResolutionProof,Boolean]): Boolean = {
//      if (!visitedProofs.contains(p)) {
//        val result = p match {
//          case Input(_) => true
//          case Resolvent(l, r) => {
//            if (!pivotsAbove.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) println("Non-regular atom: " + p.asInstanceOf[Resolvent].pivot._1.atom + " ; id: " + p.id + " ; number of children: " + p.children.length)
//                                !pivotsAbove.contains(p.asInstanceOf[Resolvent].pivot._1.atom) &&
//                                isRegularRec(l, pivotsAbove.clone + p.asInstanceOf[Resolvent].pivot._1.atom, visitedProofs) &&
//                                isRegularRec(r, pivotsAbove.clone + p.asInstanceOf[Resolvent].pivot._1.atom, visitedProofs)
//          }
//        }
//        visitedProofs += (p -> result)
//        return result
//      }
//      else return visitedProofs(p)
//    }
//    isRegularRec(proof, new HashSet[Atom], new HashMap[ResolutionProof,Boolean])
//  }

  def getNonRegularNodes(proof: ResolutionProof) = {
    def getNonRegularNodesRec(p: ResolutionProof, pivotsBelow: HashSet[Atom]) : HashSet[Int] = {
      p match {
        case Input(_) => new HashSet[Int]
        case Resolvent(l,r) => {
          val pivotsBelowNext = pivotsBelow.clone + p.asInstanceOf[Resolvent].pivot._1.atom
          val setL = getNonRegularNodesRec(l,pivotsBelowNext)
          val setR = getNonRegularNodesRec(r,pivotsBelowNext)
          val setUnion = setL.clone.union(setR)
          if (pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) setUnion += p.id
          return setUnion
        }
      }
    }
    getNonRegularNodesRec(proof, new HashSet[Atom])
  }

  def isRegular(proof: ResolutionProof) = {
    def isRegularRec(p: ResolutionProof, pivotsBelow: HashSet[Atom]): Boolean = {
      p match {
        case Input(_) => true
        case Resolvent(l, r) => {
          if (pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) println("Non-regular atom: " + p.asInstanceOf[Resolvent].pivot._1.atom + " ; id: " + p.id + " ; number of children: " + p.children.length)
          val pivotsBelowNext = pivotsBelow.clone + p.asInstanceOf[Resolvent].pivot._1.atom
          !pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom) &&
          isRegularRec(l, pivotsBelowNext) &&
          isRegularRec(r, pivotsBelowNext)
        }
      }
    }
    isRegularRec(proof, new HashSet[Atom])
  }


  def isNonTree(proof: ResolutionProof)  = {
    def isNonTreeRec(p: ResolutionProof): Boolean = p match {
      case Input(_) => p.children.length > 1
      case Resolvent(l, r) =>  p.children.length > 1 || isNonTreeRec(l) || isNonTreeRec(r)
    }
    isNonTreeRec(proof)
  }


//  def regularize(proof:ResolutionProof): Unit = {
//    if (proof.isInstanceOf[Resolvent]) {
//      val n = proof.asInstanceOf[Resolvent]
//
//        for (child <- n.children) {
//          val string = n.literalsBelow.get(child) match {case None => "NONE"; case Some(set) => set.toString}
//          println("id" + child.id + " -> " + string)
//        }
//
//      if (allChildrenAreVisited(proof)) {
//        if (proof.children.length > 1) {
//          println("MORE THAN ONE CHILD!!!")
//          println(proof.clause)
//          val literalsBelow = (for (child <- proof.children) yield proof.literalsBelow(child)).toList
//          val intersectionOfLiteralsBelow = intersection(literalsBelow)
//          println("INTERSECTION :" + intersectionOfLiteralsBelow)
//          val problematicLiterals = union(literalsBelow).diff(intersectionOfLiteralsBelow)
//          println("Problematic: " + problematicLiterals)
//
//          def findProblematicLiteralsAbove(literals: HashSet[Literal], p: ResolutionProof, visitedProofs: HashMap[ResolutionProof, Boolean]): Boolean = {
//            if (!visitedProofs.contains(p)) {
//              val result = p match {
//                case Input(c) => false
//                case Resolvent(l,r) => {
//                  if (literals.contains(p.asInstanceOf[Resolvent].pivot._1) || literals.contains(p.asInstanceOf[Resolvent].pivot._2)) {
//                    println("found problematic pivot (" + p.asInstanceOf[Resolvent].pivot + ") in node id" + p.id)
//                    true
//                  }
//                  else (findProblematicLiteralsAbove(literals, l, visitedProofs) || findProblematicLiteralsAbove(literals, r, visitedProofs))
//                }
//              }
//              visitedProofs += (p -> result)
//              return result
//            }
//            else return visitedProofs(p)
//          }
//
//          if (problematicLiterals.isEmpty || !findProblematicLiteralsAbove(problematicLiterals, n, new HashMap[ResolutionProof,Boolean])) {
//            println("did not find problematic literals...")
//            deleteSubProofIfNecessaryAndCallRecursively(intersectionOfLiteralsBelow)
//          }
//          else {
//            println("found problematic literals...")
//            for (child <- n.children.tail) {
//              val newProof = n.duplicate
//              newProof.children = child::Nil
//              newProof.literalsBelow += (child -> n.literalsBelow(child))
//              if (child.left == proof) child.left = newProof
//              else child.right = newProof
//              regularize(newProof)
//            }
//            n.children = n.children.head::Nil
//            val headLB = n.literalsBelow(n.children.head)
//            n.literalsBelow = new HashMap[Resolvent, HashSet[Literal]]
//            n.literalsBelow += (n.children.head -> headLB)
//            regularize(n)
//          }
//        }
//        else if (proof.children.length == 0) {
//          deleteSubProofIfNecessaryAndCallRecursively(new HashSet[Literal])
//        }
//        else {
//          val literalsBelow = n.literalsBelow.head._2
//          deleteSubProofIfNecessaryAndCallRecursively(literalsBelow)
//        }
//        def deleteSubProofIfNecessaryAndCallRecursively(literalsBelow: HashSet[Literal]) = {
//          def deleteNewSink(sink: ResolutionProof): Unit = sink match {
//            case Input(_) =>
//            case Resolvent(l, r) => {
//              println("deleting sink: " + sink.id)
//              l.children = l.children - sink.asInstanceOf[Resolvent]
//              r.children = r.children - sink.asInstanceOf[Resolvent]
//              if (l.children.length == 0) deleteNewSink(l)
//              else regularize(l)
//              if (r.children.length == 0) deleteNewSink(r)
//              else regularize(r)
//            }
//          }
//          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
//            println("new pivot: " + n.pivot._1)
//            n.left.literalsBelow += (n -> (literalsBelow.clone + n.pivot._2))
//            n.right.literalsBelow += (n -> (literalsBelow.clone + n.pivot._1))
//          }
//          else if (literalsBelow.contains(n.pivot._1)) {
//            println("deleting left parent: " + n.left.id)
//            n.left.children = n.left.children - n
//            println("remaining children of the deleted parent: " + n.left.children.map(child => child.id))
//            if (n.left.children.length == 0) deleteNewSink(n.left)
//            n.left = deletedSubProof
//            n.right.literalsBelow += (n -> literalsBelow)
//          }
//          else { // if (literalsBelow.contains(n.pivot._2))
//            println("deleting right parent: " + n.right.id)
//            n.right.children = n.right.children - n
//            println("remaining children of the deleted parent: " + n.right.children.map(child => child.id))
//            if (n.right.children.length == 0) deleteNewSink(n.right)
//            if (n.right.children.length == 1 && !(n.right.literalsBelow.get(n.right.children.head) == None )) regularize(n.right)
//            n.right = deletedSubProof
//            n.left.literalsBelow += (n -> literalsBelow)
//          }
//          regularize(n.left)
//          regularize(n.right)
//        }
//
//      }
//    }
//  }
//
//  def recyclePivot(proof:ResolutionProof): Unit = {
//    if (proof.isInstanceOf[Resolvent]) {
//      val n = proof.asInstanceOf[Resolvent]
//      if (allChildrenAreVisited(proof)) {
//        if (proof.children.length > 1) {
//          n.left.literalsBelow += (n -> new HashSet[Literal])
//          n.right.literalsBelow += (n -> new HashSet[Literal])
//        }
//        else if (proof.children.length == 0) {
//          n.left.literalsBelow += (n -> (new HashSet[Literal] + n.pivot._2))
//          n.right.literalsBelow += (n -> (new HashSet[Literal] + n.pivot._1))
//        }
//        else {
//          val literalsBelow = n.literalsBelow.get(n.children.head) match {case Some(set) => set; case None => throw new Exception("Literals Below was not initialized properly") }
//          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
//            n.left.literalsBelow += (n -> (literalsBelow.clone + n.pivot._2))
//            n.right.literalsBelow += (n -> (literalsBelow.clone + n.pivot._1))
//          }
//          else if (literalsBelow.contains(n.pivot._1)) {
//            n.left.children = n.left.children - n
//            n.left = deletedSubProof
//            n.right.literalsBelow += (n -> literalsBelow)
//          }
//          else { // if (literalsBelow.contains(n.pivot._2))
//            n.right.children = n.right.children - n
//            n.right = deletedSubProof
//            n.left.literalsBelow += (n -> literalsBelow)
//          }
//        }
//        regularize(n.left)
//        regularize(n.right)
//      }
//    }
//  }

    def regularize2(proof:ResolutionProof): Unit = {
      val regularizedProofs = new HashSet[ResolutionProof]
      def regularizeRec(p: ResolutionProof, callingChild: Resolvent, litB: Option[HashSet[Literal]]): Unit = {
        p match {
          case Input(_) => return
          case Resolvent(left,right) => {
            if (callingChild == null) { // Root of the Proof
              doRegularize(litB.asInstanceOf[Some[HashSet[Literal]]].get)
            }
            else {
              println("Calling Child: " + callingChild.id )
              litB match {
                case None => p.children = p.children - callingChild   // Calling Child is orphan of the called Parent
                case Some(literalsB) => p.literalsBelow += (callingChild -> literalsB)
              }
              def hasReceivedAllCalls = {
                p.children.forall(c => p.literalsBelow.contains(c))
              }
              if (hasReceivedAllCalls) {
                val lBPerChild = (for (child <- p.children) yield p.literalsBelow(child)).toList
                val intersection = intersect(lBPerChild)
                val union = unite(lBPerChild)
                val criticalLiterals = union.clone.diff(intersection)
                def occursAbove(lit: Literal) = {
                  val visitedProofs = new HashMap[ResolutionProof, Boolean]
                  def occursAboveRec(n: ResolutionProof): Boolean = n match {
                    case Input(_) => false
                    case Resolvent(l,r) => {
                      if (visitedProofs.contains(n)) visitedProofs(n)
                      else {
                        val r = n.asInstanceOf[Resolvent]
                        val result = r.pivot._1 == lit ||
                                     r.pivot._2 == lit ||
                                     occursAboveRec(l) ||
                                     occursAboveRec(r)
                        visitedProofs += (n -> result)
                        result
                      }
                    }
                  }
                  occursAboveRec(p)
                }
                val problematicLiterals = criticalLiterals.clone.filter(l => occursAbove(l))
                println(litB)
                println(lBPerChild)
                println(union)
                println(intersection)
                println(criticalLiterals)
                println(problematicLiterals)
                if (problematicLiterals.size != 0) duplicateAndRegularize
                else doRegularize(intersection)
              }
            }
            def duplicateAndRegularize = {
              for (c <- p.children.tail) {
                val newProof = p.duplicate
                newProof.children = c::Nil
                p.children = p.children - c
                p.literalsBelow -= c
                regularizeRec(newProof, c, Some(p.literalsBelow(c)))
              } 
              doRegularize(p.literalsBelow(p.children.head))
            }

            def doRegularize(literalsBelow: HashSet[Literal]) = {
              try require(!regularizedProofs.contains(p))
              catch {case _ => println(p.id + " ; " + p.children.map(c => c.id)); throw new Exception}
              
              
              val r = p.asInstanceOf[Resolvent]
              println(p.id + "(" + left.id + "," + right.id + ") " + p.children.map(c => c.id) + " , " + r.pivot + " , " + literalsBelow)
              if (!literalsBelow.contains(r.pivot._1) && !literalsBelow.contains(r.pivot._2)) {
                println("Alright!")
                regularizeRec(left, r, Some(literalsBelow.clone + r.pivot._2))
                regularizeRec(right, r, Some(literalsBelow.clone + r.pivot._1))

              }
              else if (literalsBelow.contains(r.pivot._1)) {
                println("Irregular Left")
                regularizeRec(left, r, None)
                r.left = deletedSubProof
                regularizeRec(right, r, Some(literalsBelow.clone))
              }
              else {
                require(literalsBelow.contains(r.pivot._2))
                println("Irregular Right")
                regularizeRec(right, r, None)
                r.right = deletedSubProof
                regularizeRec(left, r, Some(literalsBelow.clone))
              }
              regularizedProofs += p
            }
          }
        }
      }
      regularizeRec(proof, null, Some(new HashSet[Literal]))
    }


    def regularize(proof:ResolutionProof, message: String ): Unit = {
    if (proof.isInstanceOf[Resolvent]) {
      val n = proof.asInstanceOf[Resolvent]
        println(message)
        for (child <- n.children) {
          val string = n.literalsBelow.get(child) match {case None => "NONE"; case Some(set) => set.toString}
          println("id" + child.id + " -> " + string)
        }

      if (allChildrenAreVisited(proof)) {
        if (proof.children.length > 1) {
          println("MORE THAN ONE CHILD!!!")
          println(proof.clause)
          val literalsBelow = (for (child <- proof.children) yield proof.literalsBelow(child)).toList
          val intersectionOfLiteralsBelow = intersect(literalsBelow)
          println("INTERSECTION :" + intersectionOfLiteralsBelow)
          val problematicLiterals = unite(literalsBelow).diff(intersectionOfLiteralsBelow)
          println("Problematic: " + problematicLiterals)

          def findProblematicLiteralsAbove(literals: HashSet[Literal], p: ResolutionProof, visitedProofs: HashMap[ResolutionProof, Boolean]): Boolean = {
            if (!visitedProofs.contains(p)) {
              val result = p match {
                case Input(c) => false
                case Resolvent(l,r) => {
                  println("Searching problematic literals: node id" + p.id + ", pivot " +
                          p.asInstanceOf[Resolvent].pivot + ": " +
                          literals.contains(p.asInstanceOf[Resolvent].pivot._1) + ", " +
                          literals.contains(p.asInstanceOf[Resolvent].pivot._2))
                  if (literals.contains(p.asInstanceOf[Resolvent].pivot._1) || literals.contains(p.asInstanceOf[Resolvent].pivot._2)) {
                    println("found problematic pivot (" + p.asInstanceOf[Resolvent].pivot + ") in node id" + p.id)
                    true
                  }
                  else (findProblematicLiteralsAbove(literals, l, visitedProofs) || findProblematicLiteralsAbove(literals, r, visitedProofs))
                }
              }
              visitedProofs += (p -> result)
              return result
            }
            else return visitedProofs(p)
          }

          if (problematicLiterals.isEmpty || !findProblematicLiteralsAbove(problematicLiterals, n, new HashMap[ResolutionProof,Boolean])) {
            println("did not find problematic literals...")
            deleteSubProofIfNecessaryAndCallRecursively(intersectionOfLiteralsBelow)
          }
          else {
            println("found problematic literals...")
            for (child <- n.children.tail) {
              val newProof = n.duplicate
              newProof.children = child::Nil
              newProof.literalsBelow += (child -> n.literalsBelow(child))
              if (child.left == proof) child.left = newProof
              else child.right = newProof
              regularize(newProof, "regularizing new duplicate of proof id" + n.id + "w.r.t. child id" + child.id)
            }
            n.children = n.children.head::Nil
            val headLB = n.literalsBelow(n.children.head)
            n.literalsBelow = new HashMap[Resolvent, HashSet[Literal]]
            n.literalsBelow += (n.children.head -> headLB)
            regularize(n, "redoing regularization after duplication. W.r.t. child id" + n.children.head.id)
          }
        }
        else if (proof.children.length == 0) {
          deleteSubProofIfNecessaryAndCallRecursively(new HashSet[Literal])
        }
        else {
          val literalsBelow = n.literalsBelow.head._2
          deleteSubProofIfNecessaryAndCallRecursively(literalsBelow)
        }
        def deleteSubProofIfNecessaryAndCallRecursively(literalsBelow: HashSet[Literal]) = {
          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
            println("new pivot: " + n.pivot._1)
            n.left.literalsBelow += (n -> (literalsBelow.clone + n.pivot._2))
            n.right.literalsBelow += (n -> (literalsBelow.clone + n.pivot._1))
          }
          else if (literalsBelow.contains(n.pivot._1)) {
            println("deleting left parent: " + n.left.id)
            println("pivot: " + n.pivot._1)
            n.left.children = n.left.children - n
            println("remaining children of the deleted parent: " + n.left.children.map(child => child.id))
            regularize(n.left, "regularizing orphan parent. called by id" + n.id)
            n.left = deletedSubProof
            n.right.literalsBelow += (n -> literalsBelow.clone)
          }
          else { // if (literalsBelow.contains(n.pivot._2))
            println("deleting right parent: " + n.right.id)
            println("pivot: " + n.pivot._2)
            n.right.children = n.right.children - n
            println("remaining children of the deleted parent: " + n.right.children.map(child => child.id))
            regularize(n.right, "regularizing orphan parent. called by id" + n.id)
            n.right = deletedSubProof
            n.left.literalsBelow += (n -> literalsBelow.clone)
          }
          regularize(n.left, "regularizing left parent. called by id" + n.id)
          regularize(n.right, "regularizing right parent. called by id" + n.id)
        }

      }
    }
  }

  def recyclePivot(proof:ResolutionProof): Unit = {
    if (proof.isInstanceOf[Resolvent]) {
      val n = proof.asInstanceOf[Resolvent]
      if (allChildrenAreVisited(proof)) {
        if (proof.children.length > 1) {
          n.left.literalsBelow += (n -> new HashSet[Literal])
          n.right.literalsBelow += (n -> new HashSet[Literal])
        }
        else if (proof.children.length == 0) {
          n.left.literalsBelow += (n -> (new HashSet[Literal] + n.pivot._2))
          n.right.literalsBelow += (n -> (new HashSet[Literal] + n.pivot._1))
        }
        else {
          val literalsBelow = n.literalsBelow.get(n.children.head) match {case Some(set) => set; case None => throw new Exception("Literals Below was not initialized properly") }
          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
            n.left.literalsBelow += (n -> (literalsBelow.clone + n.pivot._2))
            n.right.literalsBelow += (n -> (literalsBelow.clone + n.pivot._1))
          }
          else if (literalsBelow.contains(n.pivot._1)) {
            n.left.children = n.left.children - n
            n.left = deletedSubProof
            n.right.literalsBelow += (n -> literalsBelow)
          }
          else { // if (literalsBelow.contains(n.pivot._2))
            n.right.children = n.right.children - n
            n.right = deletedSubProof
            n.left.literalsBelow += (n -> literalsBelow)
          }
        }
        recyclePivot(n.left)
        recyclePivot(n.right)
      }
    }
  }

  def fixProof(proof:ResolutionProof) = fixProofRec(proof, new HashSet[ResolutionProof])
  private def fixProofRec(proof:ResolutionProof, visitedProofs: HashSet[ResolutionProof]) : Unit = {
    if (!visitedProofs.contains(proof)) {
      visitedProofs += proof
      proof match {
        case Input(c) => return
        case Resolvent(left,right) => {
          val n = proof.asInstanceOf[Resolvent]
          fixProofRec(left, visitedProofs)
          fixProofRec(right, visitedProofs)
          if (left.clause.contains(n.pivot._1) && right.clause.contains(n.pivot._2)) {
            n.clause = resolve(left.clause, right.clause)
          }
          else {
            val survivingParent : ResolutionProof =
            if (left == deletedSubProof) right
            else if (right == deletedSubProof) left
            else if (left.clause.contains(n.pivot._1) && !right.clause.contains(n.pivot._2)) right
            else if (!left.clause.contains(n.pivot._1) && right.clause.contains(n.pivot._2)) left
            else {
              if (proofLength(left) < proofLength(right)) left
              else right
            }
            for (child <- n.children) {
              if (child.left == n) child.left = survivingParent
              else child.right = survivingParent
            }
          }
        }
      }
    }
  }

  def allChildrenAreVisited(proof:ResolutionProof): Boolean = {
    if (proof.isInstanceOf[Resolvent]) {
      println("Have All Children of id" + proof.id + " ( id" + proof.asInstanceOf[Resolvent].left.id +  " , id" + proof.asInstanceOf[Resolvent].right.id + " ) Been Visited? : " + (proof.children.length == proof.literalsBelow.size) )
    }
    proof.children.length == proof.literalsBelow.size 
  }
}
