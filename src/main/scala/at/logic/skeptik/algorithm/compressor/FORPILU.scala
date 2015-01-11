package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.judgment.immutable.{ SetSequent => IClause }
import at.logic.skeptik.expression._
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import collection.Map
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
import at.logic.skeptik.proof.sequent.resolution.Contraction
import at.logic.skeptik.proof.sequent.resolution.CanRenameVariables
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents

abstract class FOAbstractRPILUAlgorithm
  extends AbstractRPILUAlgorithm with FindDesiredSequent with CanRenameVariables {

  protected def checkForRes(safeLiteralsHalf: Set[E], aux: E): Boolean = {

    if (safeLiteralsHalf.size < 1) {
      return false
    }

    /* 
     * unifiableVars might not contain the variables in the aux formulae. When UR(MRR) generates the auxL/auxR formulae,
     * it may rename the variables in one premise to a new premise that we just haven't seen yet (and which is resolved out
     * in that resolution and thus never really visible in the proof, so we need to check for new variables and
     * add them to our list of unifiable variables or the unification might fail.
     */

    /*  For example,
     * 
     *  p(X) |- q(a)     with    q(X) |- 
     * 
     *  UR might rename the right X as Y, then resolve out to get P(X) |-
     *  And while UR used q(Y) |- and recorded the aux formula as such, it didn't rename
     *  the right premise, so we never see the variable Y, even though it can be unified.
     */

    for (safeLit <- safeLiteralsHalf) {
      unify((aux, safeLit) :: Nil)(getSetOfVars(aux)) match {
        case Some(_) => {
          return true
        }
        case None => {
          //Do nothing
        }
      }
    }
    false
  }

  class FOEdgesToDelete extends EdgesToDelete {

    override def nodeIsMarked(node: SequentProofNode): Boolean = {
      // may be optimized (edgesToDelete contains node is checked 3 times)
      node match {
        case _ if ((edges contains node) && edges(node)._2) => true
        case UnifyingResolution(left, right, _, _) if (isMarked(node, left) && isMarked(node, right)) =>
          deleteNode(node)
          true
        case _ => false
      }
    }

    override protected def sideOf(parent: SequentProofNode, child: SequentProofNode) = child match {
      case UnifyingResolution(left, right, _, _) => if (parent == left) LeftDS
      else if (parent == right) RightDS
      else throw new Exception("Unable to find parent in child")
      case _ => throw new Exception("This function should never be called with child not being a UR")
    }

  }

  protected def isMRRContraction(c: Contraction): Boolean = {
    if (c.premises.size == 1) {
      c.premises.head match {
        case UnifyingResolutionMRR(_, _, _, _) => return true
        case _ => return false
      }
    }
    false
  }

  // Main functions
  protected def fixProofNodes(edgesToDelete: EdgesToDelete, unifiableVariables: MSet[Var], auxMap: MMap[SequentProofNode, E], mguMap: MMap[SequentProofNode, Substitution])(p: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
    lazy val fixedLeft = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;

    var resMap = new MMap[SequentProofNode, MSet[Substitution]]()
    //    println("auxMap: " + auxMap)
    p match {
      case Axiom(conclusion) => p

      case Contraction(_, _) if isMRRContraction(p.asInstanceOf[Contraction]) => {
        val mrr = p.premises.head
        fixProofNodes(edgesToDelete, unifiableVariables, auxMap, mguMap)(mrr, fixedPremises)
      }

      // If we've got a proof of false, we propagate it down the proof
      case UnifyingResolution(_, _, _, _) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) => {
        fixedLeft
      }

      case UnifyingResolution(_, _, _, _) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) => {
        fixedRight
      }

      // Delete nodes and edges
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, left) => {
        //        println("using fixedRight - " + fixedRight)
        val sub = p.asInstanceOf[UnifyingResolution].mgu
        val al = p.asInstanceOf[UnifyingResolution].auxL
        val ar = p.asInstanceOf[UnifyingResolution].auxR
        println("al: " + al)
        println("ar: " + ar)
        //        println(" which would have been used after this sub: " + sub)
        //        val newNode = new FOSubstitution(fixedRight, sub)(unifiableVariables)
        //        println("to be this: " + newNode)
        val set = resMap.get(p)
        if (set.isEmpty) {
          val newSet = MSet[Substitution](sub)
          resMap.put(p, newSet)
        } else {
          set.get.add(sub)
        }

        fixedRight
        //newNode
      }
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, right) => {
        println("using fixedLeft - " + fixedLeft)
        fixedLeft
      }

      // If premises haven't been changed, we keep the proof as is (memory optimization)
      case UnifyingResolution(left, right, _, _) if (left eq fixedLeft) && (right eq fixedRight) => p

      case UnifyingResolution(left, right, pivot, _) if (desiredFound(fixedLeft.conclusion, p.conclusion)(unifiableVariables)) => {
        //If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
        //the fixed parent; so the pivot better be missing.
        assert(!checkForRes(fixedLeft.conclusion.toSetSequent.suc, pivot))
        fixedLeft
      }
      case UnifyingResolution(left, right, _, pivot) if (desiredFound(fixedRight.conclusion, p.conclusion)(unifiableVariables)) => {
        //If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
        //the fixed parent; so the pivot better be missing.
        assert(!checkForRes(fixedLeft.conclusion.toSetSequent.ant, pivot))
        fixedRight
      }

      // Main case (rebuild a resolution)
      case UnifyingResolution(left, right, auxL, auxR) => {
//        println("Error found")
        println("auxL: " + auxL)
        println("auxR: " + auxR)
        println("l: " + left)
        println("r: " + right)
        println("fl: " + fixedLeft)
        println("fr: " + fixedRight)
        //TODO: use map for lookup, find carry, and build new expected result, use that to fix ambiguity
        //   --- necessary now? 

        val nonEmptyLeftMap = !auxMap.get(left).isEmpty && !mguMap.get(left).isEmpty
        val nonEmptyRightMap = !auxMap.get(right).isEmpty && !mguMap.get(right).isEmpty

        if(nonEmptyRightMap) {
          println("right is non empty!") //TODO: at some point, I'll need to finish this case.
        }
        
        //        if (nonEmptyLeftMap) {
        //          //TODO: what if there are multiple 'oldMGU's? e.g. from left and right
        //          val oldMGU = mguMap.get(left).get
        //          println("old mgu      : " + oldMGU)
        //          println("new mgu      : " + p.asInstanceOf[UnifyingResolution].mgu)
        //          println("ncL          : " + auxMap.get(left).get)
        //          println("ncL (applied): " + mguMap.get(left).get(auxMap.get(left).get))
        //
        //          //TODO: generalize this call/move it
        //          fixAmbiguous(fixedLeft, fixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
        //
        //        }
        //
        //        if (nonEmptyRightMap) {
        //          println("ncR: " + mguMap.get(right).get(auxMap.get(right).get))
        //        }

        val ambiguousErrorString = "Resolution (MRR): the resolvent is ambiguous."

        //TODO: clean this up?
        try {
//          println("error - first")
          UnifyingResolutionMRR(fixedRight, fixedLeft)(unifiableVariables)
        } catch {
          case e: Exception => {
            println("error - second " + e.getMessage())
            if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) {
              if (nonEmptyLeftMap && !nonEmptyRightMap) {
                val oldMGU = mguMap.get(left).get
                fixAmbiguous(fixedLeft, fixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
              } else {
                //TODO: change this branch
                println("STUB HIT -- probably not correct!")
                UnifyingResolutionMRR(fixedLeft, fixedRight)(unifiableVariables) //stub
              }
            } else {

              try {
                UnifyingResolutionMRR(fixedLeft, fixedRight)(unifiableVariables)
              } catch {
                case e: Exception if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) => {
                    val oldMGU = mguMap.get(left).get
                    fixAmbiguous(fixedLeft, fixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
                }
                case e: Exception => {
                  println("ERROR")
                  throw new Exception("BAD!")
                }
              }
            }
          }
        }

      }

      // When the inference is not UR, nothing is done 
      case _ => {
        println("ignoring: " + p) //TODO: remove
        p
      }
    }
  }

  def fixAmbiguous(fLeft: SequentProofNode, fRight: SequentProofNode, oldMGU: Substitution, left: SequentProofNode, right: SequentProofNode, auxL: E, auxR: E)(implicit unifiableVariables: MSet[Var]) = {
    val newMGU = unify((auxL, auxR) :: Nil).get //should always be non-empty

    val leftEq = !fLeft.equals(left)
    val rightEq = !fRight.equals(right)

    val fLeftClean = if (!fLeft.equals(left)) {
      new FOSubstitution(fLeft, oldMGU).conclusion
    } else {
      fLeft.conclusion
    }
    val leftRemainder = findRemainder(fLeftClean, auxL, oldMGU, leftEq)
    println("leftRemainder: " + leftRemainder)

    val fRightClean = if (!fRight.equals(right)) {
      new FOSubstitution(fRight, oldMGU).conclusion
    } else {
      fRight.conclusion
    }
    val rightRemainder = findRemainder(fRightClean, auxR, oldMGU, rightEq)

    //TODO: this for the left? 
    //TODO: do this conditionally only?
    val rightRemainderWithNewMGU = (new FOSubstitution(Axiom(rightRemainder), newMGU)).conclusion
    println("rightRemainder: " + rightRemainder)
    println("rrwithnewmgu :  " + rightRemainderWithNewMGU)

    val tempLeft = Axiom(leftRemainder)
    val tempRight = Axiom(rightRemainderWithNewMGU)
    val cleanLeftRemainder = fixSharedNoFilter(tempLeft, tempRight, 0, unifiableVariables).conclusion

    val newTarget = rightRemainderWithNewMGU.union(cleanLeftRemainder)
    println("newTarget: " + newTarget)

    val finalLeft = if (leftEq) {
      new FOSubstitution(fLeft, oldMGU)
    } else {
      fLeft
    }

    val finalRight = if (rightEq) {
      new FOSubstitution(fRight, oldMGU)
    } else {
      fRight
    }

    val out = try {
      UnifyingResolution(finalLeft, finalRight, newTarget)
    } catch {
      case e: Exception => {
        UnifyingResolution(finalRight, finalLeft, newTarget)
      }
    }
    println("okay... " + out)

    out
  }

  def findRemainder(seq: Sequent, target: E, mgu: Substitution, applySub: Boolean)(implicit unifiableVariables: MSet[Var]): Sequent = {
    //TODO: what if the target is in both ant and suc?? Should only be removed once. 
    //Need to track where it is, and only remove it from that.
    val out = addAntecedents(checkHalf(seq.ant, target, mgu, applySub).toList) union addSuccedents(checkHalf(seq.suc, target, mgu, applySub).toList)
    //    (new FOSubstitution(Axiom(out), mgu)).conclusion
    out
  }

  def checkHalf(half: Seq[E], target: E, sub: Substitution, applySub: Boolean)(implicit unifiableVariables: MSet[Var]): Seq[E] = {
    if (half.size == 0) {
      Seq[E]()
    } else {
      val found = if (applySub) { sub(half.head) =+= target } else { half.head =+= target }
      if (found) {
        half.tail
      } else {
        Seq[E](half.head) ++ checkHalf(half.tail, target, sub, applySub)
      }
    }
  }

}

abstract class FOAbstractRPIAlgorithm
  extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  protected def safeLiteralsFromChild(childWithSafeLiterals: (SequentProofNode, IClause),
    parent: SequentProofNode, edgesToDelete: FOEdgesToDelete) =
    childWithSafeLiterals match {
      case (child @ UnifyingResolution(left, right, _, auxR), safeLiterals) if left == parent =>
        if (edgesToDelete.isMarked(child, right)) safeLiterals else addLiteralSmart(safeLiterals, auxR, false, left, right)
      case (child @ UnifyingResolution(left, right, auxL, _), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child, left)) safeLiterals else addLiteralSmart(safeLiterals, auxL, true, left, right)

      case (_, safeLiterals) => safeLiterals
      // Unchecked Inf case _ => throw new Exception("Unknown or impossible inference rule")
    }

  protected def addLiteralSmart(seq: IClause, aux: E, addToAntecedent: Boolean, left: SequentProofNode, right: SequentProofNode): IClause = {
    //Restrict MartelliMontanari to tell whether "aux" is more general (and not just unifiable) 
    // by passing only the variables of "aux" as unifiable variables.
    val uVars = new MSet[Var]() union getSetOfVars(aux)
    val seqHalf = if (addToAntecedent) {
      seq.ant
    } else {
      seq.suc
    }
    for (lit <- seqHalf) {
      unify((lit, aux) :: Nil)(uVars) match {
        case None => {}
        case Some(_) => { return seq }
      }
    }
    if (addToAntecedent) {
      aux +: seq
    } else {
      seq + aux
    }
  }

  protected def computeSafeLiterals(proof: SequentProofNode,
    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
    edgesToDelete: FOEdgesToDelete): IClause

}

trait FOCollectEdgesUsingSafeLiterals
  extends FOAbstractRPIAlgorithm {

  protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
    val edgesToDelete = new FOEdgesToDelete()
    var auxMap = new MMap[SequentProofNode, E]()
    var mguMap = new MMap[SequentProofNode, Substitution]()
    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      println("SAFE LITERALS for " + p + " => " + safeLiterals)
      p match {
        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.suc, auxL)) => {
          //          println("p: " + p + " and right: " + right + " edge marked")
          //          println("other edge: " +  left + " and mgu " + p.asInstanceOf[UnifyingResolution].mgu)
          println("p, auxL: " + p + "   " + auxL)
          auxMap.put(p, auxL)
          mguMap.put(p, p.asInstanceOf[UnifyingResolution].mgu)
          edgesToDelete.markRightEdge(p)

        }
        case UnifyingResolution(left, right, auxL, auxR) if checkForRes(safeLiterals.ant, auxR) => {
          println("p: " + p + " and right: " + left + " edge marked")
          println("other edge: " + right + " and mgu " + p.asInstanceOf[UnifyingResolution].mgu)
          println("p, auxR: " + p + "   " + auxR)

          auxMap.put(p, auxR)
          mguMap.put(p, p.asInstanceOf[UnifyingResolution].mgu)
          edgesToDelete.markLeftEdge(p)
        }
        case _ =>
      }
      (p, safeLiterals)
    }
    nodeCollection.bottomUp(visit)
    (edgesToDelete, auxMap, mguMap)
  }
}

trait FOUnitsCollectingBeforeFixing
  extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  protected def getAllVars(proof: Proof[SequentProofNode]): MSet[Var] = {
    val out = MSet[Var]()
    for (n <- proof) {
      val vars = getSetOfVars(n)
      for (v <- vars) {
        out += v
      }
    }
    out
  }
}

trait FOIntersection
  extends FOAbstractRPIAlgorithm {
  protected def computeSafeLiterals(proof: SequentProofNode,
    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
    edgesToDelete: FOEdgesToDelete): IClause = {
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof) } match {
      case Nil =>
        if (!childrensSafeLiterals.isEmpty) edgesToDelete.markBothEdges(proof)
        proof.conclusion.toSetSequent
      case h :: t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) => acc intersect safeLiteralsFromChild(v, proof, edgesToDelete) }
    }
  }
}