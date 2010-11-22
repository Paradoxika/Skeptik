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

  def getNodeById(p: ResolutionProof, id: Int, visitedProofs: HashMap[ResolutionProof, ResolutionProof]): ResolutionProof = {
    if (visitedProofs.contains(p)) return visitedProofs(p)
    else {
      var result: ResolutionProof = null
      if (p.id == id) result = p
      else {
        p match {
          case Input(_) => return null
          case Resolvent(l,r) => {
            val lR = getNodeById(l, id, visitedProofs)
            if (lR != null) result = lR
            else {
              val rR = getNodeById(r, id, visitedProofs)
              if (rR != null) result = rR
            }
          }
        }
      }
      visitedProofs += (p -> result)
      return result
    }
  }

  def getNonRegularNodes(proof: ResolutionProof) = {
    def getNonRegularNodesRec(p: ResolutionProof, pivotsBelow: List[Atom]) : List[Int] = {
      p match {
        case Input(_) => Nil
        case Resolvent(l,r) => {
          if (p.asInstanceOf[Resolvent].pivot._1.atom == "v115") println(p.id)
          val pivotsBelowNext = p.asInstanceOf[Resolvent].pivot._1.atom::pivotsBelow
          val listL = getNonRegularNodesRec(l,pivotsBelowNext)
          val listR = getNonRegularNodesRec(r,pivotsBelowNext)
          if (pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) {
            println(p.id + " (" + p.asInstanceOf[Resolvent].left.id + "," + p.asInstanceOf[Resolvent].right.id + ") " + p.asInstanceOf[Resolvent].pivot + " : " + pivotsBelow)
            return p.id::(listL:::listR)
          }
          else return listL:::listR
        }
      }
    }
    getNonRegularNodesRec(proof, Nil)
  }

    def getUnvisitedNodes(proof: ResolutionProof) = {
    def getUnvisitedNodesRec(p: ResolutionProof) : List[(Int,Int,Int)] = {
      p match {
        case Input(_) => Nil
        case Resolvent(l,r) => {
          val listL = getUnvisitedNodesRec(l)
          val listR = getUnvisitedNodesRec(r)
          if (p.expectedNumberOfCalls != p.numberOfCalls) return (p.id, p.expectedNumberOfCalls, p.numberOfCalls)::(listL:::listR)
          else return listL:::listR
        }
      }
    }
    getUnvisitedNodesRec(proof)
  }

  def isRegular(proof: ResolutionProof) = {
    def isRegularRec(p: ResolutionProof, pivotsBelow: List[Atom]): Boolean = {
      p match {
        case Input(_) => true
        case Resolvent(l, r) => {
          if (pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) println("Non-regular atom: " + p.asInstanceOf[Resolvent].pivot._1.atom + " ; id: " + p.id + " ; number of children: " + p.children.length)
          val pivotsBelowNext = p.asInstanceOf[Resolvent].pivot._1.atom::pivotsBelow
          !pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom) &&
          isRegularRec(l, pivotsBelowNext) &&
          isRegularRec(r, pivotsBelowNext)
        }
      }
    }
    isRegularRec(proof, Nil)
  }


  def isNonTree(proof: ResolutionProof)  = {
    def isNonTreeRec(p: ResolutionProof): Boolean = p match {
      case Input(_) => p.children.length > 1
      case Resolvent(l, r) =>  p.children.length > 1 || isNonTreeRec(l) || isNonTreeRec(r)
    }
    isNonTreeRec(proof)
  }

  def regularize(proof:ResolutionProof): Unit = {

    //val n640 = getNodeById(proof, 640, new HashMap[ResolutionProof,ResolutionProof])
    //val n740 = getNodeById(proof, 740, new HashMap[ResolutionProof,ResolutionProof])
    val n573 = getNodeById(proof, 573, new HashMap[ResolutionProof,ResolutionProof])
    val n586 = getNodeById(proof, 586, new HashMap[ResolutionProof,ResolutionProof])
    val n343 = getNodeById(proof, 343, new HashMap[ResolutionProof,ResolutionProof])

    val regularizedProofs = new HashSet[ResolutionProof]
    def regularizeRec(p: ResolutionProof, callingChild: Resolvent, litB: Option[List[Literal]]): Unit = {


      //val debug = isBelow(n740,p) && isBelow(p,n640)
      val debug = isBelow(n586,p) && isBelow(p,n573)
      //val debug = isBelow(n343,p) && isBelow(p,n573)
      def dP(s: Any) = {
        //if ((p.isInstanceOf[Resolvent] && p.asInstanceOf[Resolvent].pivot._1.atom == "v208") || List(155, 132, 893, 889, 887, 885, 881, 878, 842, 840, 837, 833, 825, 823, 821, 819, 93, 274, 597, 555, 573, 640).contains(p.id)) {
        if (debug) {
          println(s)
        }
      }
      if (p.numberOfCalls == 0) {
        if (p.children.length > 0) p.expectedNumberOfCalls = p.children.length
        else p.expectedNumberOfCalls = 1 // p is root
      }
      p.numberOfCalls += 1

      //dP(p.expectedNumberOfCalls)
      //dP(p.numberOfCalls)

      p match {
        case Input(_) => return
        case Resolvent(left,right) => {
          if ((p.asInstanceOf[Resolvent].pivot._1.atom == "v208"))

          try {require(p.numberOfCalls <= p.expectedNumberOfCalls)}
          catch {
            case _ => {
              println("Expected Calls: " + p.expectedNumberOfCalls + " ; numberOfCalls: " + p.numberOfCalls)
              println(p.id + "(" + p.asInstanceOf[Resolvent].left.id + "," + p.asInstanceOf[Resolvent].right.id + ")" + p.children.map(c => c.id))
              throw new Exception
            }
          }


          if (callingChild == null) { // Root of the Proof
            dP("null calling child")
            doRegularize(litB.asInstanceOf[Some[List[Literal]]].get)
          }
          else {
            dP("")
            dP("Calling Child: " + callingChild.id )
            dP("Called node: id" + p.id)
            litB match {
              case None => p.children = p.children - callingChild   // Calling Child is orphan of the called Parent
              case Some(literalsB) => p.literalsBelow += (callingChild -> literalsB)
            }
            def hasReceivedAllCalls = {
              p.children.forall(c => p.literalsBelow.contains(c))
            }
            if (hasReceivedAllCalls) {
              require( (p.expectedNumberOfCalls == p.numberOfCalls) )
              val lBPerChild = (for (child <- p.children) yield p.literalsBelow(child)).toList
              val intersection = intersect(lBPerChild)
              val union = unite(lBPerChild)
              val criticalLiterals = union.diff(intersection)
              val problematicLiterals = criticalLiterals.filter(l => p.pivotAtomsAbove.contains(l.atom))
              val r = p.asInstanceOf[Resolvent]
              dP(p.id + "(" + left.id + "," + right.id + ") " + p.children.map(c => c.id) + " , " + r.pivot)

              //dP("litB: " + litB)
              //dP("lBPerChild: " + lBPerChild)
              dP("union: " + union)
              //dP("intersection: " + intersection)
              //dP("critical: " + criticalLiterals)
              //dP("pivotAtomsAbove: " + p.pivotAtomsAbove)
              dP("problematic: " + problematicLiterals)
              if (problematicLiterals.length != 0) duplicateAndRegularize
              else doRegularize(union)
            }
          }
          def duplicateAndRegularize = {
            for (c <- p.children) {
              dP(c.id + " -> " + p.literalsBelow(c))
            }

            for (c <- p.children.tail) {
              val newProof = p.duplicate
              newProof.children = c::Nil
              if (c.left == p) c.left = newProof
              else c.right = newProof
              p.children = p.children - c
              val literalsBelowForNewProof = p.literalsBelow(c)
              p.literalsBelow -= c
              dP("duplicate: " + newProof.id)
              //dP(newProof.clause)
              //dP(p.clause)
              //dP(p.literalsBelow.get(c))
              regularizeRec(newProof, c, Some(literalsBelowForNewProof))
            }
            for (c <- p.children) {
              dP(c.id + " -> " + p.literalsBelow(c))
            }
            dP(p.literalsBelow(p.children.head))
            doRegularize(p.literalsBelow(p.children.head))
          }

          def doRegularize(literalsBelow: List[Literal]) = {
            try require(!regularizedProofs.contains(p))
            catch {case _ => println("id" + p.id + " ; " + p.children.map(c => c.id) + " " + regularizedProofs.map(n => n.id) + regularizedProofs.map(n => n.equals(p)) + regularizedProofs.contains(p)); throw new Exception("scheiße")}
            val r = p.asInstanceOf[Resolvent]
            dP("id" + p.id + " is going to be regularized")
            if (!literalsBelow.contains(r.pivot._1) && !literalsBelow.contains(r.pivot._2)) {
              dP("Alright!")
              dP("literalsBelowLeft: " + r.pivot._2::literalsBelow)
              dP("literalsBelowRight: " + r.pivot._1::literalsBelow)
              regularizeRec(left, r, Some(r.pivot._2::literalsBelow))
              regularizeRec(right, r, Some(r.pivot._1::literalsBelow))

            }
            else if (literalsBelow.contains(r.pivot._1)) {
              dP("Irregular Left")
              regularizeRec(left, r, None)
              r.left = deletedSubProof
              dP("literalsBelowRight: " + literalsBelow)
              regularizeRec(right, r, Some(literalsBelow))
            }
            else {
              require(literalsBelow.contains(r.pivot._2))
              dP("Irregular Right")
              regularizeRec(right, r, None)
              r.right = deletedSubProof
              dP("literalsBelowLeft: " + literalsBelow)
              regularizeRec(left, r, Some(literalsBelow))
            }
            regularizedProofs += p
            dP("id" + p.id + " was regularized and added")
          }
        }
      }
    }
    regularizeRec(proof, null, Some(Nil))
  }



  def recyclePivot(proof:ResolutionProof): Unit = {
    if (proof.isInstanceOf[Resolvent]) {
      val n = proof.asInstanceOf[Resolvent]
      if (allChildrenAreVisited(proof)) {
        if (proof.children.length > 1) {
          n.left.literalsBelow += (n -> Nil)
          n.right.literalsBelow += (n -> Nil)
        }
        else if (proof.children.length == 0) {
          n.left.literalsBelow += (n -> (n.pivot._2::Nil))
          n.right.literalsBelow += (n -> (n.pivot._1::Nil))
        }
        else {
          val literalsBelow = n.literalsBelow.get(n.children.head) match {case Some(set) => set; case None => throw new Exception("Literals Below was not initialized properly") }
          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
            n.left.literalsBelow += (n -> (n.pivot._2::literalsBelow ))
            n.right.literalsBelow += (n -> (n.pivot._1::literalsBelow))
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
          if (n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) {
            n.clause = resolve(n.left.clause, n.right.clause)
          }
          else {
            if (n.id == 573 || n.id == 574) {
              println(n.id)
              println(left == deletedSubProof)
              println(right == deletedSubProof)
            }
            val survivingParent : ResolutionProof =
            if (n.left == deletedSubProof) n.right
            else if (n.right == deletedSubProof) n.left
            else if (n.left.clause.contains(n.pivot._1) && !n.right.clause.contains(n.pivot._2)) n.right
            else if (!n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) n.left
            else {
              if (proofLength(n.left) < proofLength(n.right)) n.left
              else n.right
            }
            if (n.id == 573 || n.id == 574) {
              println(survivingParent.id)
            }
            for (child <- n.children) {
              if (n.id == 573 || n.id == 574) {
                println("updating child")
                println(child.id)
                println(child.left == n)
                println(child.right == n)
              }
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
