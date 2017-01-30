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
import at.logic.skeptik.proof.sequent.resolution.FindMGU
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents

abstract class FOAbstractRPILUAlgorithm
    extends AbstractRPILUAlgorithm with FindDesiredSequent with CanRenameVariables with FindMGU {

  protected def checkContracted(old: Sequent, fixed: Sequent): Boolean = {
    var antMissing = false
    for (oldAnt <- old.ant) {
      var litFound = false
      for (fixAnt <- fixed.ant) {
        val uvars = getSetOfVars(oldAnt) union getSetOfVars(fixAnt)
        unify((oldAnt, fixAnt) :: Nil)(uvars) match {
          case Some(_) => {
            litFound = true
          }
          case None => {
            //Do nothing
          }
        }
      }
      if (!litFound) {
        antMissing = true
      }
    }
    var sucMissing = false
    for (oldSuc <- old.suc) {
      var litFound = false
      for (fixSuc <- fixed.suc) {
        val uvars = getSetOfVars(oldSuc) union getSetOfVars(fixSuc)
        unify((oldSuc, fixSuc) :: Nil)(uvars) match {
          case Some(_) => {
            litFound = true
          }
          case None => {
            //Do nothing
          }
        }
      }
      if (!litFound) {
        sucMissing = true
      }
    }

    return antMissing || sucMissing

  }

  //(jgorzny) 2 June 2015:
  //This checks the aux after the original mgu was applied
  //prevents some terrible attempts to lower
  //NOTE: p MUST be a unifying resolution node
  protected def checkForResSmart(safeLiteralsHalf: Set[E], aux: E, p: SequentProofNode, skip: Boolean = false): Boolean = {
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

    def oldMGU = p.asInstanceOf[UnifyingResolution].mgu
    def newAux = if (!skip) { oldMGU(aux) } else { aux }
    for (safeLit <- safeLiteralsHalf) {
      val uvars = (getSetOfVars(newAux) union getSetOfVars(safeLit))
      unify((newAux, safeLit) :: Nil)(uvars) match {
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

  def getPredName(lit: E): String = {
    lit match {
      case App(f, a) => {
        getPredName(f)
      }
      case Abs(f, a) => {
        getPredName(f)
      }
      case Var(n, _) => {
        n
      }
    }

  }

  def checkAll(lits: Set[E], safe: E): Boolean = {
    val sName = getPredName(safe)
    for (lit <- lits) {
      val lName = getPredName(lit)
      if (lName.equals(sName)) {
        val vars = getSetOfVars(safe)
        val sigma = unify((lit, safe) :: Nil)(vars)
        if (sigma.isEmpty) {
          return false
        }
      }
    }
    true
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
        case _                                 => return false
      }
    }
    false
  }

  //ensure that the node that will be replacing the unifying resolution is entirely safe  
  protected def finalCheck(safeLit: Sequent, seqToDelete: Sequent, allowSubset: Boolean): Boolean = {

    def desiredIsContained(safe: Sequent, toDelete: Sequent): Boolean = {
      if (checkIfConclusionsAreEqual(safe, toDelete)) {
        return true
      } else if (toDelete.ant.toSet.subsetOf(safe.ant.toSet) && toDelete.suc.toSet.subsetOf(safe.suc.toSet)) {
        return true
      } else {
        val cVars = getSetOfVars(toDelete.ant: _*) union getSetOfVars(toDelete.suc: _*)

        val (mapIsUniquelyValid, intersectedMap) = computeIntersectedMap(safe, toDelete, cVars, allowSubset)

        if (mapIsUniquelyValid) {
          if (!checkMapSub(intersectedMap, cVars, toDelete, safe)) {
            return false
          } else {
            return true
          }
        } else {
          return checkInvalidMap(intersectedMap, cVars, toDelete, safe, true)

        }
      }
    }

    def antVars = getSetOfVars(seqToDelete.ant: _*)
    def sucVars = getSetOfVars(seqToDelete.suc: _*)
    def antVarsB = getSetOfVars(safeLit.ant: _*)
    def sucVarsB = getSetOfVars(safeLit.suc: _*)
    def allvars = MSet[Var]() ++ antVars ++ sucVars ++ antVarsB ++ sucVarsB
    def safeClean = fixSharedNoFilter(Axiom(safeLit), Axiom(seqToDelete), 0, allvars)
    def vars = MSet[Var]() ++ antVars ++ sucVars

    val allMatchesOkay = checkAllPairs(seqToDelete, safeClean.conclusion)

    if (fastFindRenaming(safeClean.conclusion, seqToDelete, false) != null) {
      allMatchesOkay
    } else {
      desiredIsContained(safeClean.conclusion, seqToDelete) && allMatchesOkay
    }

  }

  def checkAllPairs(seqToDelete: Sequent, safe: Sequent): Boolean = {
    var out = true
    for (a <- seqToDelete.ant) {
      out = out && checkAll(safe.ant.toSet, a)
    }
    for (a <- seqToDelete.suc) {
      out = out && checkAll(safe.suc.toSet, a)
    }
    out
  }

  // Main functions
  protected def fixProofNodes(edgesToDelete: EdgesToDelete, unifiableVariables: MSet[Var], 
                              safeMap: MMap[SequentProofNode, Sequent])(p: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
    lazy val fixedLeft = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;

    var resMap = new MMap[SequentProofNode, MSet[Substitution]]()
    p match {

      case Contraction(_, _) if isMRRContraction(p.asInstanceOf[Contraction]) => {
        try {
          val out = Contraction(fixedLeft, p.conclusion)(unifiableVariables)
          p //if we can find the old conclusion from the fixed node, it's the same. memory optimization
        } catch {
          case t: Throwable => {
            if (!checkContracted(p.conclusion, fixedLeft.conclusion)) {
              fixedLeft
            } else {
              p
            }
          }
        }
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
        fixedRight
      }
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, right) => {
        fixedLeft
      }

      // If premises haven't been changed, we keep the proof as is (memory optimization)
      case UnifyingResolution(left, right, _, _) if (left eq fixedLeft) && (right eq fixedRight) => {
        try {
          val lDistinct = Sequent(fixedLeft.conclusion.ant.distinct: _*)(fixedLeft.conclusion.suc.distinct: _*)
          val newL = Contraction(fixedLeft, lDistinct)(unifiableVariables)

          val rDistinct = Sequent(fixedRight.conclusion.ant.distinct: _*)(fixedRight.conclusion.suc.distinct: _*)
          val newR = Contraction(fixedRight, rDistinct)(unifiableVariables)

          if (checkIfConclusionsAreEqual(newR, fixedRight) && checkIfConclusionsAreEqual(newL, fixedLeft)) {
            return p
          }

          val k = UnifyingResolutionMRR(newL, newR)(unifiableVariables)

          k
        } catch {
          case a: Throwable => {
            p
          }
        }
      }

      case UnifyingResolution(left, right, pivot, _) if (findRenaming(fixedLeft.conclusion, p.conclusion)(unifiableVariables) != null) => {
        //If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
        //the fixed parent; so the pivot better be missing.
        assert(!checkForResSmart(fixedLeft.conclusion.toSetSequent.suc, pivot, p))
        fixedLeft
      }
      case UnifyingResolution(left, right, _, pivot) if (findRenaming(fixedRight.conclusion, p.conclusion)(unifiableVariables) != null) => {
        //If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
        //the fixed parent; so the pivot better be missing.
        assert(!checkForResSmart(fixedRight.conclusion.toSetSequent.ant, pivot, p))
        fixedRight
      }

      // Main case (rebuild a resolution)
      case UnifyingResolution(left, right, auxL, auxR) => {

        val ambiguousErrorStringMRR = "Resolution (MRR): the resolvent is ambiguous."
        val ambiguousErrorString = "Resolution: the resolvent is ambiguous."

        val out = try {

          if (checkIfConclusionsAreEqual(fixedRight, fixedLeft)) {
            val rProofSize = Proof[SequentProofNode](fixedRight).size
            val lProofSize = Proof[SequentProofNode](fixedLeft).size
            if (rProofSize > lProofSize) {
              fixedLeft
            } else {
              fixedRight
            }
          } else {

            val res = UnifyingResolutionMRR(fixedLeft, fixedRight)(unifiableVariables)
            res
          }

        } catch {
          case e: Exception => {
            if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) {
                fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, p.conclusion, false)(unifiableVariables)
            } else {
              try {
                val a = UnifyingResolution(fixedRight, fixedLeft)(unifiableVariables)
                a
              } catch {
                case f: Exception => {
                  val a = attemptGreedyContraction(contractIfHelpful(fixedLeft)(unifiableVariables), fixedRight,
                    fixedRight, ambiguousErrorString, ambiguousErrorStringMRR, left, right, auxL, auxR, p.conclusion)(unifiableVariables)
                  a
                }
              }
            }
          }
        }

        val oldSafe = safeMap.get(p).get

        val bothEq = checkIfConclusionsAreEqual(fixedLeft, left) && checkIfConclusionsAreEqual(fixedRight, right)

        if (finalCheck(oldSafe, out.conclusion, true) || bothEq) {
          out
        } else {
          //fixedRight
          if (checkIfConclusionsAreEqual(fixedLeft, left)) {
            fixedRight
            if (finalCheck(oldSafe, fixedRight.conclusion, true)) {
              fixedRight
            } else {
              out
            }
          } else if (checkIfConclusionsAreEqual(fixedRight, right)) {
            fixedLeft
            if (finalCheck(oldSafe, fixedLeft.conclusion, true)) {
              fixedLeft
            } else {
              out
            }
          } else {
            out
          }
        }
      }

      // When the inference is not UR, nothing is done 
      case _ => {
        p
      }
    }
  }

  def attemptGreedyContraction(fixedLeft: SequentProofNode, fixedRight: SequentProofNode, newFixedRight: SequentProofNode,
                               ambiguousErrorString: String, ambiguousErrorStringMRR: String, left: SequentProofNode, right: SequentProofNode, auxL: E, auxR: E,
                               oldConclusion: Sequent)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

    try {
      UnifyingResolution(fixedLeft, newFixedRight)(unifiableVariables)
    } catch {
      case e: Exception if (e.getMessage() != null && (e.getMessage.contains(ambiguousErrorString) || e.getMessage.contains(ambiguousErrorStringMRR))) => {
        try {
          if (checkIfConclusionsAreEqual(contractIfHelpful(fixedLeft)(unifiableVariables), left) && checkIfConclusionsAreEqual(contractIfHelpful(fixedRight)(unifiableVariables), right)) {
            //If the fixed are the same as the old, nothing is changed in this part. Use the old conclusion as a goal
            //to fix the ambiguity; greedy contraction risks the proof failing to end with the empty sequent.
            val success = UnifyingResolution(contractIfHelpful(fixedLeft)(unifiableVariables), contractIfHelpful(fixedRight)(unifiableVariables), oldConclusion)(unifiableVariables)
            return success
          }
          if (checkIfConclusionsAreEqual(fixedLeft, left) && checkIfConclusionsAreEqual(fixedRight, right)) {
            //If the fixed are the same as the old, nothing is changed in this part. Use the old conclusion as a goal
            //to fix the ambiguity; greedy contraction risks the proof failing to end with the empty sequent.
            val success = UnifyingResolution(fixedLeft, fixedRight, oldConclusion)(unifiableVariables)
            return success
          }
          return fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, true)(unifiableVariables)
        } catch {
          case h: Exception => {
            //do nothing; we'll do something else below
          }
        }
        try {
          val k = UnifyingResolutionMRR(fixedLeft, contractIfHelpful(fixedRight)(unifiableVariables))(unifiableVariables)
          k
        } catch {
          case f: Exception => {
            fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, false)(unifiableVariables)
          }
        }

      }
      case e: Exception => {
        val oldConclusionIsNotEmpty = !(oldConclusion.ant.size == 0 && oldConclusion.suc.size == 0)
        if (checkIfConclusionsAreEqual(fixedRight, fixedLeft)) {
          fixedRight
        } else if (checkSubsetOrEquality(true, fixedRight.conclusion, oldConclusion)) {
          fixedRight
        } else if (checkSubsetOrEquality(true, fixedLeft.conclusion, oldConclusion)) {
          fixedLeft
        } else {

          try {

            val out =
              if (contractFixedFindsTarget(fixedLeft, oldConclusion) != null) {
                val t = contractFixedFindsTarget(fixedLeft, oldConclusion)
                t
              } else if (contractFixedFindsTarget(fixedRight, oldConclusion) != null) {
                val t = contractFixedFindsTarget(fixedRight, oldConclusion)
                t
              } else {

                try {
                  UnifyingResolutionMRR(newFixedRight, fixedLeft)(unifiableVariables)
                } catch {
                  case g: Exception => {
                    g.printStackTrace()
                    UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables)
                  }
                }
              }
            out
          } catch {
            case f: Exception => {
              f.printStackTrace()
              fixedLeft

            }
          }

        }
      }
    }
  }

  def contractFixedFindsTarget(premise: SequentProofNode, seq: Sequent)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    try {
      if (checkIfConclusionsAreEqual(premise.conclusion, seq)) {
        premise
      } else {
        if (seq.ant.size != 0 || seq.suc.size != 0) {
          val out = Contraction(premise, seq)(unifiableVariables)
          out
        } else {
          premise
        }
      }
    } catch {
      case _: Throwable => {
        null
      }
    }
  }

  def makeFOSub(premise: SequentProofNode, sub: Substitution)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    val FOSub = new FOSubstitution(premise, sub)
    if (checkIfConclusionsAreEqual(FOSub, premise)) {
      premise
    } else {
      FOSub
    }
  }

  def tryGreedyContraction(left: SequentProofNode, right: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    try {
      val quickFix = UnifyingResolution(Contraction(left), right)
      return quickFix
    } catch {
      case _: Throwable => { //do nothing
      }
    }

    val quickFixReverse = UnifyingResolution(left, Contraction(right))

    return quickFixReverse

  }

  def fixAmbiguous(fLeft: SequentProofNode, fRight: SequentProofNode, left: SequentProofNode, right: SequentProofNode,
                   auxL: E, auxR: E, oldConclusion: Sequent, skip: Boolean)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

    if (!skip) {
      try {
        val quickFix = tryGreedyContraction(fLeft, fRight)
        return quickFix
      } catch {
        case _: Throwable => { //do nothing - we have work to do.
        }
      }
    }

    val aVars = getSetOfVars(auxL) union getSetOfVars(auxR)
    val newMGU = unify((auxL, auxR) :: Nil)(aVars).get //should always be non-empty

    val leftEq = findRenaming(fLeft, left) != null
    val rightEq = findRenaming(fLeft, left) != null

    val fLeftClean = fLeft.conclusion 

    
    val (leftRemainder, leftSub) = findRemainder(fLeftClean, auxL, Substitution(), leftEq, false)
    val fRightClean = fRight.conclusion

    val (rightRemainder, rightSub) = findRemainder(fRightClean, auxR, Substitution(), rightEq, true)
    val rightRemainderWithNewMGU = makeFOSub(Axiom(rightRemainder), newMGU).conclusion
    val tempLeft = makeFOSub(makeFOSub(Axiom(leftRemainder), leftSub), newMGU)

    val tempRight = Axiom(rightRemainderWithNewMGU)
    val cleanLeftRemainder = fixSharedNoFilter(tempLeft, tempRight, 0, unifiableVariables).conclusion

    val newTarget = rightRemainderWithNewMGU.union(tempLeft.conclusion)   

    val newFinalRight = findTargetIfEqual(rightEq, right, fLeft)
    val newFinalLeft = findTargetIfEqual(leftEq, left, fRight)

    val out =
      try {
        try {
          val o = UnifyingResolutionMRR(newFinalLeft, newFinalRight, oldConclusion)
          o
        } catch {
          case e: Exception => {
            if (e.getMessage.contains("Cannot find desired resolvent")) {
              UnifyingResolution(contractIfHelpful(newFinalLeft), contractIfHelpful(newFinalRight), contractIfHelpful(Axiom(oldConclusion)).conclusion)
            } else {
              UnifyingResolution(fRight, fLeft)
            }
          }
        }
      } catch {
        case f: Exception => {
          UnifyingResolutionMRR(fLeft, fRight, newTarget)
        }
      }
    out
  }

  def findTargetIfEqual(equal: Boolean, oldPremise: SequentProofNode,
                        newPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    if (equal) {
      try {
        findTarget(oldPremise, newPremise)
      } catch {
        case _: Throwable => {
          newPremise
        }
      }
    } else {
      newPremise
    }
  }

  def findTarget(original: SequentProofNode, fixed: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    return Contraction(fixed, original.conclusion)

  }

  def findRemainder(seq: Sequent, target: E, mgu: Substitution, applySub: Boolean, removeFromAnt: Boolean)(implicit unifiableVariables: MSet[Var]): (Sequent, Substitution) = {
    def remove(e: E, list: List[E]) = list diff List(e)
    val (newAnt, antSub) = if (removeFromAnt) { (remove(mgu(target), seq.ant.toList), Substitution()) } else { (seq.ant.toList, null) }
    val (newSuc, sucSub) = if (!removeFromAnt) { (remove(mgu(target), seq.suc.toList), Substitution()) } else { (seq.suc.toList, null) }

    val subOut = if (antSub != null) { antSub } else { sucSub } //at least one of these must be non-empty
    //both should never be empty

    val out = addAntecedents(newAnt) union addSuccedents(newSuc)
    (out, subOut)
  }

}

abstract class FOAbstractRPIAlgorithm
    extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  def findActualAux(seqHalf: Seq[E], aux: E, mgu: Substitution): E = {
    for (s <- seqHalf) {
      if (mgu(s).equals(aux)) {
        return s
      }
    }
    aux
  }

  protected def safeLiteralsFromChild(childWithSafeLiterals: (SequentProofNode, IClause),
                                      parent: SequentProofNode, edgesToDelete: FOEdgesToDelete) = {

    childWithSafeLiterals match {
      //in these cases, 'child' is the unifying resolution
      case (child @ UnifyingResolution(left, right, auxL, auxR), safeLiterals) if left == parent =>
        if (edgesToDelete.isMarked(child, right)) {
          safeLiterals
        } else {
          val sub = child.asInstanceOf[UnifyingResolution].mgu
          def auxRb = sub(auxR)
          addLiteralSmart(safeLiterals, auxRb, false)
        }

      case (child @ UnifyingResolution(left, right, auxL, auxR), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child, left)) {
          safeLiterals
        } else {
          val sub = child.asInstanceOf[UnifyingResolution].mgu
          def auxLb = sub(auxL)
          addLiteralSmart(safeLiterals, auxLb, true)
        }

      case (p, safeLiterals) => {
        safeLiterals
      }
    }
  }

  protected def addLiteralSmart(seq: IClause, aux: E, addToAntecedent: Boolean): IClause = {
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
        case Some(_) => {
          return seq
        }
      }
    }
    def out = if (addToAntecedent) {
      (aux +: seq)
    } else {
      (seq + aux)
    }

    out

  }

  protected def computeSafeLiterals(proof: SequentProofNode,
                                    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
                                    edgesToDelete: FOEdgesToDelete): IClause

}

trait FOCollectEdgesUsingSafeLiterals
    extends FOAbstractRPIAlgorithm with FindDesiredSequent {

  protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
    val edgesToDelete = new FOEdgesToDelete()
    val safeMap = new MMap[SequentProofNode, Sequent]()
    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      safeMap.put(p, safeLiterals.toSeqSequent)
      p match {
       
        
        case UnifyingResolution(left, right, auxL, auxR) if (checkForResSmart(safeLiterals.suc, auxR, p) &&        
          finalCheck(safeLiterals.toSeqSequent, left.conclusion, false)) => {
          edgesToDelete.markRightEdge(p)
        }
        case UnifyingResolution(left, right, auxL, auxR) if (checkForResSmart(safeLiterals.ant, auxL, p) &&
          finalCheck(safeLiterals.toSeqSequent, right.conclusion, false)) => {
          edgesToDelete.markLeftEdge(p)
        }
        case _ =>
      }
      (p, safeLiterals)
    }
    nodeCollection.bottomUp(visit)
    (edgesToDelete, safeMap)
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
        if (!childrensSafeLiterals.isEmpty) {
          edgesToDelete.markBothEdges(proof)
        }
        proof.conclusion.toSetSequent
      case h :: t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) =>
          {
            smartIntersect(acc, safeLiteralsFromChild(v, proof, edgesToDelete))
          }
        }
    }
  }

  protected def smartIntersect(l: IClause, r: IClause) = {
    var out = Sequent()()
    val uVars = getSetOfVars(l.toSeqSequent) union getSetOfVars(r.toSeqSequent)
    for (la <- l.ant) {
      for (ra <- r.ant) {
        unify((la, ra) :: Nil)(uVars) match {
          case None => {}
          case Some(sub) => {
            val newLA = getCleanLiteral(la, sub, out)
            out = newLA +: out
          }
        }
      }
    }

    for (ls <- l.suc) {
      for (rs <- r.suc) {
        unify((ls, rs) :: Nil)(uVars) match {
          case None => {}
          case Some(sub) => {
            val newLS = getCleanLiteral(ls, sub, out)
            out = out + newLS
          }
        }
      }
    }

    out.toSetSequent

  }

  def getCleanLiteral(l: E, s: Substitution, rest: Sequent) = {
    val restAx = Axiom(rest)
    val lsubbed = s(l)
    val lsAx = Axiom(Sequent(lsubbed)())
    val vars = getSetOfVars(rest) union getSetOfVars(lsubbed)

    val lsAxClean = fixSharedNoFilter(lsAx, restAx, 0, vars)

    val cleanL = lsAxClean.conclusion.ant.head

    cleanL
  }
}
