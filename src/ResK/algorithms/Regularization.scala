package ResK.algorithms

import ResK.calculi.resolution._
import scala.collection._

object Regularization {

  def removeUnusedResolvents(proof: Proof): Proof = {
    println("removing unused resolvents")
    proof.duplicate
  }

  def getIrregularNodes(proof: Proof) = {
    def getIrregularNodesRec(p: Proof, pivotsBelow: List[Atom]) : List[Proof] = {
      p match {
        case Input(_) => Nil
        case Resolvent(l,r) => {
          val pivotsBelowNext = p.asInstanceOf[Resolvent].pivot._1.atom::pivotsBelow
          val listL = getIrregularNodesRec(l,pivotsBelowNext)
          val listR = getIrregularNodesRec(r,pivotsBelowNext)
          if (pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) {
            //println(p.id + " (" + p.asInstanceOf[Resolvent].left.id + "," + p.asInstanceOf[Resolvent].right.id + ") " + p.asInstanceOf[Resolvent].pivot + " : " + pivotsBelow)
            return p::(listL:::listR)
          }
          else return listL:::listR
        }
      }
    }
    getIrregularNodesRec(proof, Nil)
  }

  def isRegular(proof: Proof) = {
    def isRegularRec(p: Proof, pivotsBelow: List[Atom]): Boolean = {
      p match {
        case Input(_) => true
        case Resolvent(l, r) => {
          //if (pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) println("Non-regular atom: " + p.asInstanceOf[Resolvent].pivot._1.atom + " ; id: " + p.id + " ; number of children: " + p.children.length)
          val pivotsBelowNext = p.asInstanceOf[Resolvent].pivot._1.atom::pivotsBelow
          !pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom) &&
          isRegularRec(l, pivotsBelowNext) &&
          isRegularRec(r, pivotsBelowNext)
        }
      }
    }
    isRegularRec(proof, Nil)
  }



  private def doRegularize(p: Resolvent, criticalLiterals: mutable.HashSet[Literal], continuation: Resolvent => Unit) = {
    //println("doRegularize: " + p.id)
    if (!criticalLiterals.contains(p.pivot._1) && !criticalLiterals.contains(p.pivot._2)) {
      //println("here1")
      regularizationRecSchema(p.left, p, Some(criticalLiterals + p.pivot._2), continuation)
      regularizationRecSchema(p.right, p, Some(criticalLiterals + p.pivot._1), continuation)
    }
    else if (criticalLiterals.contains(p.pivot._1)) {
      //println("here2")
      regularizationRecSchema(p.left, p, None, continuation)
      deletedSubProof replacesAsParentOf (p.left, p)
      regularizationRecSchema(p.right, p, Some(criticalLiterals), continuation)
    }
    else {
      //println("here3")
      regularizationRecSchema(p.right, p, None, continuation)
      deletedSubProof replacesAsParentOf (p.right, p)

      
      regularizationRecSchema(p.left, p, Some(criticalLiterals), continuation)
    }
  }

  private def regularizationRecSchema(p: Proof, callingChild: Resolvent, litB: Option[mutable.HashSet[Literal]], continuation: Resolvent => Unit): Unit = {
    //println(p.id)
    //println(p.isInstanceOf[Input])
    p match {
      case Input(_) => return
      case Resolvent(left,right) => {
        val r = p.asInstanceOf[Resolvent]

        //println("regrec matched resolvent")
        //println("litB" + litB)

        litB match {
          case None => p.children = p.children - callingChild   // Calling Child is orphan of the called Parent
          case Some(literalsB) => {
            //println("ok")
            val literals = p.literalsBelow 
            //for (l <- literals) println("literals: " + l)
            //println("ok2")
            literals += (callingChild -> literalsB)
          }
        }
        //def hasReceivedAllCalls = p.children.forall(c => p.literalsBelow.contains(c)) // inefficient
        def hasReceivedAllCalls = p.children.length == p.literalsBelow.size
        if (hasReceivedAllCalls) continuation(r)
      }
    }
  }

  
  def unite[T](list: List[mutable.HashSet[T]]): mutable.HashSet[T] = list match {
    case Nil => new mutable.HashSet[T]
    case head::tail => unite(tail) ++ head
  }
  def intersect[T](list: List[mutable.HashSet[T]]): mutable.HashSet[T] = {
    list match {
      case Nil => new mutable.HashSet[T]
      case head::Nil => head
      case head::tail => head.intersect(intersect(tail))
    }
  }


  def recyclePivots(p:Proof): Proof = {
    if (p.isInstanceOf[Resolvent]) doRegularize(p.asInstanceOf[Resolvent], new mutable.HashSet[Literal], recyclePivotsContinuation)
    p
  }
  private def recyclePivotsContinuation: Resolvent => Unit = r => {
    val criticalLiterals = if (r.children.length == 1) r.literalsBelow(r.children.head) // case where r has only one child
                           else new mutable.HashSet[Literal]                                                    // case where r has zero or many children
    r.forgetLiteralsBelow
    r.forgetClause
    doRegularize(r, criticalLiterals, recyclePivotsContinuation)
  }


  def recyclePivotsWithIntersection(p:Proof): Proof = {
    if (p.isInstanceOf[Resolvent]) doRegularize(p.asInstanceOf[Resolvent], new mutable.HashSet[Literal], recyclePivotsWithIntersectionContinuation)
    p
  }
  private def recyclePivotsWithIntersectionContinuation: Resolvent => Unit = r => {
    val criticalLiterals = if (r.children.length == 1) r.literalsBelow(r.children.head) // case where r has only one child
                           else if (r.children.length > 1) {                            // case where r has many children
                             val lBPerChild = (for (child <- r.children) yield r.literalsBelow(child)).toList
                             intersect(lBPerChild)
                           }
                           else new mutable.HashSet[Literal] // case where r has zero children
    r.forgetLiteralsBelow
    r.forgetClause
    doRegularize(r, criticalLiterals, recyclePivotsWithIntersectionContinuation)
  }


  def regularizeNaive(p: Proof): Proof = {
    if (p.isInstanceOf[Resolvent]) doRegularize(p.asInstanceOf[Resolvent], new mutable.HashSet[Literal], fullyRegularizeContinuation(doNotFilterCriticalLiterals, simpleDuplicateAndRegularizeDuplicates))
    p
  }
  def regularizeWithOnlyRootDuplication(p: Proof): Proof = {
    if (p.isInstanceOf[Resolvent]) doRegularize(p.asInstanceOf[Resolvent], new mutable.HashSet[Literal], fullyRegularizeContinuation(doNotFilterCriticalLiterals, duplicateOnlyRootAndRegularizeDuplicates))
    p
  }
  def regularize = p => regularizeWithOnlyRootDuplication(p)

  private def fullyRegularizeContinuation(filterCriticalLiterals: mutable.HashSet[Literal] => mutable.HashSet[Literal], duplicateAndRegularizeDuplicates: (mutable.HashSet[Literal] => mutable.HashSet[Literal]) => Resolvent => mutable.HashSet[Literal] => Unit): Resolvent => Unit = r => {
    val lBPerChild = (for (child <- r.children) yield r.literalsBelow(child)).toList
    val intersection = intersect(lBPerChild)
    val union = unite(lBPerChild)
    val criticalLiterals = filterCriticalLiterals(union.diff(intersection))
    if (criticalLiterals.size != 0) duplicateAndRegularizeDuplicates(filterCriticalLiterals)(r)(criticalLiterals)
    else doRegularize(r, intersection, fullyRegularizeContinuation(filterCriticalLiterals, duplicateAndRegularizeDuplicates))
  }

  private def doNotFilterCriticalLiterals(criticalLiterals: mutable.HashSet[Literal]) = criticalLiterals
  private def simpleDuplicateAndRegularizeDuplicates(filterCriticalLiterals: mutable.HashSet[Literal] => mutable.HashSet[Literal])(r: Resolvent)(criticalLiterals: mutable.HashSet[Literal]):Unit = {
    for (c <- r.children.tail) {
      val newProof = r.duplicate
      newProof.children = c::Nil
      if (c.left == r) c.left = newProof
      else c.right = newProof
      r.children = r.children - c
      val literalsBelowForNewProof = r.literalsBelow(c)
      r.literalsBelow -= c
      regularizationRecSchema(newProof, c, Some(literalsBelowForNewProof), fullyRegularizeContinuation(filterCriticalLiterals, simpleDuplicateAndRegularizeDuplicates))
    }
    doRegularize(r, r.literalsBelow(r.children.head), fullyRegularizeContinuation(filterCriticalLiterals, simpleDuplicateAndRegularizeDuplicates))
  }
  private def duplicateOnlyRootAndRegularizeDuplicates(filterCriticalLiterals: mutable.HashSet[Literal] => mutable.HashSet[Literal])(r: Resolvent)(criticalLiterals: mutable.HashSet[Literal]):Unit = {
    for (c <- r.children.tail) {
      val newProof = r.duplicateRoot
      newProof.children = c::Nil
      if (c.left == r) c.left = newProof
      else c.right = newProof
      r.children = r.children - c
      val literalsBelowForNewProof = r.literalsBelow(c)
      r.literalsBelow -= c
      regularizationRecSchema(newProof, c, Some(literalsBelowForNewProof), fullyRegularizeContinuation(filterCriticalLiterals, duplicateOnlyRootAndRegularizeDuplicates))
    }
    doRegularize(r, r.literalsBelow(r.children.head), fullyRegularizeContinuation(filterCriticalLiterals, duplicateOnlyRootAndRegularizeDuplicates))
  }
}
