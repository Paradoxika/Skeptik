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

    def getMSet(a: scala.collection.mutable.Set[Var]): MSet[Var] = {
      val out = MSet[Var]()
      for (e <- a) {
        out.add(e)
      }
      out
    }

    for (safeLit <- safeLiteralsHalf) {
      val uvars = (getSetOfVars(aux) union getSetOfVars(safeLit))
      val uvarsB = getMSet(uvars)
      val isMore = isMoreGeneral(Sequent(aux)(), Sequent(safeLit)())(uvarsB)
      //      if(areAlphaEq(safeLit, aux)(uvarsB) || isMore || safeLit.equals(aux)){
      //      if (areAlphaEq(safeLit, aux)(uvarsB)) {
      //
      //        return true
      //      }
      unify((aux, safeLit) :: Nil)(getSetOfVars(aux)) match {
        case Some(_) => {
          println("matched!!! " + aux + " AND " + safeLit)
          return true
        }
        case None => {
          //Do nothing
        }
      }
    }
    false
  }

  //june 2 mod
  //this checks the aux after the original mgu was applied
  //prevents some terrible attempts to lower
  //NOTE: p MUST be a unifying resolution node
  protected def checkForResSmartRight(safeLiteralsHalf: Set[E], aux: E, p: SequentProofNode): Boolean = {

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

    def getMSet(a: scala.collection.mutable.Set[Var]): MSet[Var] = {
      val out = MSet[Var]()
      for (e <- a) {
        out.add(e)
      }
      out
    }

    def oldMGU = p.asInstanceOf[UnifyingResolution].mgu
    def newAux = oldMGU(aux)
    println("oldMGU: " + oldMGU)
    println("newAUX: " + newAux)

    for (safeLit <- safeLiteralsHalf) {
      val uvars = (getSetOfVars(newAux) union getSetOfVars(safeLit))
      val uvarsB = getMSet(uvars)
      val isMore = isMoreGeneral(Sequent(newAux)(), Sequent(safeLit)())(uvarsB)
      unify((newAux, safeLit) :: Nil)(getSetOfVars(newAux)) match {
        case Some(_) => {
          println("matched!!! " + newAux + " AND " + safeLit)
          return true
        }
        case None => {
          //Do nothing
        }
      }
    }
    false
  }

  //june 2 mod
  //this checks the aux after the original mgu was applied
  //prevents some terrible attempts to lower
  //NOTE: p MUST be a unifying resolution node
  //TODO: merge with right case
  //TODO: test further
  protected def checkForResSmartLeft(safeLiteralsHalf: Set[E], aux: E, p: SequentProofNode): Boolean = {

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

    def getMSet(a: scala.collection.mutable.Set[Var]): MSet[Var] = {
      val out = MSet[Var]()
      for (e <- a) {
        out.add(e)
      }
      out
    }

    //TODO: this is taken DIRECTLY from FOLU. refactor it to somewhere nice
    def getRenamedMGU(original: Sequent, clean: Sequent, sub: Substitution, vars: MSet[Var]): Substitution = {
      val renamingForward = findRenaming(original, clean)(vars)
      if (renamingForward.size == 0) {
        return sub
      }

      val renamingBackward = findRenaming(clean, original)(vars)

      println("GRM: forward: " + renamingForward)
      println("GRM: backward: " + renamingBackward)

      def appSub(pair: (Var, E)): (Var, E) = {
        if (!renamingForward.get(pair._1).isEmpty) {
          (renamingForward(pair._1).asInstanceOf[Var], pair._2)
        } else if (!renamingBackward.get(pair._1).isEmpty) {
          (renamingBackward(pair._1).asInstanceOf[Var], pair._2)
        } else {
          pair
        }

      }

      val outPairs = sub.toList.map(p => appSub(p))

      Substitution(outPairs: _*)
    }

    def oldMGU = p.asInstanceOf[UnifyingResolution].mgu
    def left = p.asInstanceOf[UnifyingResolution].leftPremise
    def nodeLeftClean = p.asInstanceOf[UnifyingResolution].leftClean
    println("oldMGU: " + oldMGU)

    //maybe this stuff  isn't necessary--------
    //        println("left: " + left)
    //        println("cleanleft: " + nodeLeftClean)
    //        def vars = MSet[Var]() ++ getSetOfVars(left) ++ getSetOfVars(nodeLeftClean)
    //    
    //        val fixedMGU = getRenamedMGU(left.conclusion, nodeLeftClean.conclusion, oldMGU, vars)
    //        println("fixedMGU: " + fixedMGU)
    //-------------------

    def newAux = oldMGU(aux) // fixedMGU(aux)
    println("newAUX: " + newAux)

    for (safeLit <- safeLiteralsHalf) {
      val uvars = (getSetOfVars(newAux) union getSetOfVars(safeLit))
      val uvarsB = getMSet(uvars)
      val isMore = isMoreGeneral(Sequent(newAux)(), Sequent(safeLit)())(uvarsB)
      unify((newAux, safeLit) :: Nil)(getSetOfVars(newAux)) match {
        case Some(_) => {
          println("matched!!! " + newAux + " AND " + safeLit)
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
    p match {
      case Axiom(conclusion) => p

      case Contraction(_, _) if isMRRContraction(p.asInstanceOf[Contraction]) => {
        val mrr = p.premises.head
        fixProofNodes(edgesToDelete, unifiableVariables, auxMap, mguMap)(mrr, fixedPremises)
      }

      // If we've got a proof of false, we propagate it down the proof
      case UnifyingResolution(_, _, _, _) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) => {
        println("using fixedleft without updating mgu map " + fixedLeft)
        fixedLeft
      }

      case UnifyingResolution(_, _, _, _) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) => {
        println("using fixedRight without updating mgu map " + fixedRight)
        fixedRight
      }

      // Delete nodes and edges
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, left) => {
        //                println("using fixedRight - " + fixedRight)
        //        val al = p.asInstanceOf[UnifyingResolution].auxL
        //        val ar = p.asInstanceOf[UnifyingResolution].auxR
        //        println("al: " + al)
        //        println("ar: " + ar)
        //        println(" which would have been used after this sub: " + sub)
        //        println("to be this: " + newNode)
        //        val set = resMap.get(p)
        //        if (set.isEmpty) {
        //          val newSet = MSet[Substitution](sub)
        //          resMap.put(p, newSet)
        //        } else {
        //          set.get.add(sub)
        //        }
        println("using fixedRight updating mgu map B " + fixedRight)
        val sub = p.asInstanceOf[UnifyingResolution].mgu
        mguMap.put(fixedRight, sub)
        fixedRight

        //        val newNode = new FOSubstitution(fixedRight, sub)(unifiableVariables)        
        //        newNode
      }
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, right) => {
        println("using fixedLeft without updating mgu map B " + fixedLeft)
        val sub = p.asInstanceOf[UnifyingResolution].mgu
        //        val newNode = new FOSubstitution(fixedLeft, sub)(unifiableVariables)
        //        newNode

        mguMap.put(fixedLeft, sub)

        fixedLeft
      }

      // If premises haven't been changed, we keep the proof as is (memory optimization)
      case UnifyingResolution(left, right, _, _) if (left eq fixedLeft) && (right eq fixedRight) => {
        p
      }

      case UnifyingResolution(left, right, pivot, _) if (desiredFound(fixedLeft.conclusion, p.conclusion)(unifiableVariables)) => {
        //If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
        //the fixed parent; so the pivot better be missing.
        assert(!checkForRes(fixedLeft.conclusion.toSetSequent.suc, pivot))
        println("using fixedLeft without updating mgu map C " + fixedLeft)

        fixedLeft
      }
      case UnifyingResolution(left, right, _, pivot) if (desiredFound(fixedRight.conclusion, p.conclusion)(unifiableVariables)) => {
        //If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
        //the fixed parent; so the pivot better be missing.
        assert(!checkForRes(fixedLeft.conclusion.toSetSequent.ant, pivot))
        println("using fixedRight without updating mgu map  C " + fixedRight)
        //                mguMap.put(fixedRight, p.asInstanceOf[UnifyingResolution].mgu)
        fixedRight
      }

      // Main case (rebuild a resolution)
      case UnifyingResolution(left, right, auxL, auxR) => {
        //        println("Error found")
        //        println("RPI: auxL: " + auxL)
        //        println("RPI: auxR: " + auxR)
        //        println("l: " + left)
        //        println("r: " + right)
        //        println("fl: " + fixedLeft)
        //        println("fr: " + fixedRight)
        //TODO: use map for lookup, find carry, and build new expected result, use that to fix ambiguity
        //   --- necessary now? 

        val nonEmptyLeftMap = !auxMap.get(left).isEmpty && !mguMap.get(left).isEmpty
        val nonEmptyRightMap = !auxMap.get(right).isEmpty && !mguMap.get(right).isEmpty

        if (nonEmptyRightMap) {
          println("right is non empty!") //TODO: at some point, I'll need to finish this case.
        }

        val ambiguousErrorString = "Resolution (MRR): the resolvent is ambiguous."

        //TODO: clean this up?
        try {
          def newFixedRight = if (!mguMap.get(fixedRight).isEmpty) {
            new FOSubstitution(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
          } else {
            fixedRight
          }
          def attemptD = UnifyingResolutionMRR(newFixedRight, fixedLeft)(unifiableVariables)
          println(attemptD)
          attemptD
        } catch {
          case e: Exception => {
            println("error - second " + e.getMessage())
            if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) {
              if (nonEmptyLeftMap && !nonEmptyRightMap) {
                val oldMGU = mguMap.get(left).get
                def newFixedRight = if (!mguMap.get(fixedRight).isEmpty) {
                  new FOSubstitution(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
                } else {
                  fixedRight
                }
                def attemptC = fixAmbiguous(fixedLeft, newFixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
                println(attemptC)
                attemptC
              } else {
                //TODO: change this branch
                println("STUB HIT -- probably not correct!")
                def newFixedRight = if (!mguMap.get(fixedRight).isEmpty) {
                  new FOSubstitution(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
                } else {
                  fixedRight
                }
                UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables) //stub
              }
            } else {

              try {
                def newFixedRight = if (!mguMap.get(fixedRight).isEmpty) {
                  new FOSubstitution(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
                } else {
                  fixedRight
                }
                println("trying: " + fixedLeft + " and " + fixedRight)
                def attemptB = UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables)
                println("B: " + attemptB)
                attemptB
              } catch {
                case e: Exception if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) => {

                  try {
                    println("fixedRight: " + fixedRight)
                    println("fixedLeft:  " + fixedLeft)
                    def attempt = UnifyingResolutionMRR(fixedLeft, Contraction(fixedRight)(unifiableVariables))(unifiableVariables)
                    println(attempt)
                    attempt
                  } catch {
                    case f: Exception => {
                      println("oldmgu map: " + mguMap)
                      println("left? " + left)
                      val oldMGU = mguMap.get(left).get
                      def nonAmbig = fixAmbiguous(fixedLeft, fixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
                      println("nonambig: " + nonAmbig)
                      nonAmbig
                    }
                  }
                }
                case e: Exception => {
                  println("fixed things: " + fixedLeft + " and " + fixedRight)

                  println("ERROR " + e.getMessage())
                  println("saving mgu? " + mguMap.get(right))
                  println("saving mgu? fixed  " + mguMap.get(fixedRight))

                  //                  def subbedRight =  new FOSubstitution(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
                  //                  def testingOut = UnifyingResolution(subbedRight, fixedLeft)(unifiableVariables)
                  //                  println(testingOut)
                  println("auxMap.get(right) " + auxMap.get(right))
                  println("mguMap.get(left).isEmpty " + mguMap.get(left))
                  println("auxMap.get(left) " + auxMap.get(left))
                  println("mgumap: " + mguMap)

                  throw new Exception("BAD!")
                }
              }
            }
          }
        }

      }

      // When the inference is not UR, nothing is done 
      case _ => {
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
    val (leftRemainder, leftSub) = findRemainder(fLeftClean, auxL, oldMGU, leftEq)
    //    println("leftRemainder: " + leftRemainder)

    val fRightClean = if (!fRight.equals(right)) {
      new FOSubstitution(fRight, oldMGU).conclusion
    } else {
      fRight.conclusion
    }
    val (rightRemainder, rightSub) = findRemainder(fRightClean, auxR, oldMGU, rightEq)

    //TODO: this for the left? 
    //TODO: do this conditionally only?
    val rightRemainderWithNewMGU = (new FOSubstitution(Axiom(rightRemainder), newMGU)).conclusion
    //    println("rightRemainder: " + rightRemainder)
    //    println("rrwithnewmgu :  " + rightRemainderWithNewMGU)

    val tempLeft = new FOSubstitution(new FOSubstitution(Axiom(leftRemainder), leftSub), newMGU)
    //    println("tl: " + tempLeft)
    val tempRight = Axiom(rightRemainderWithNewMGU)
    val cleanLeftRemainder = fixSharedNoFilter(tempLeft, tempRight, 0, unifiableVariables).conclusion

    //    println("lr: " + leftRemainder)
    //    println("clr: " + cleanLeftRemainder)
    //    println("test? " + (new FOSubstitution(Axiom(cleanLeftRemainder), newMGU)))

    //        val newTarget = rightRemainderWithNewMGU.union(cleanLeftRemainder)

    val newTarget = rightRemainderWithNewMGU.union(tempLeft.conclusion)
    //    println("newTarget: " + newTarget)

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
    //    println("okay... " + out)

    out
  }

  def findRemainder(seq: Sequent, target: E, mgu: Substitution, applySub: Boolean)(implicit unifiableVariables: MSet[Var]): (Sequent, Substitution) = {
    //TODO: what if the target is in both ant and suc?? Should only be removed once. 
    //Need to track where it is, and only remove it from that.

    val (newAnt, antSub) = checkHalf(seq.ant, target, mgu, applySub)
    val (newSuc, sucSub) = checkHalf(seq.suc, target, mgu, applySub)

    val subOut = if (antSub != null) { antSub } else { sucSub } //at least one of these must be non-empty
    //both should never be empty

    val out = addAntecedents(newAnt) union addSuccedents(newSuc)
    (out, subOut)
  }

  def areAlphaEq(a: E, b: E)(implicit unifiableVariables: MSet[Var]): Boolean = {
    checkHelperAlphaManual(Seq[E](a), Seq[E](b))
  }

  def checkHalf(half: Seq[E], target: E, sub: Substitution, applySub: Boolean)(implicit unifiableVariables: MSet[Var]): (List[E], Substitution) = {
    //    if (half.size == 0) {
    //      Seq[E]()
    //    } else {
    //      
    //      val found = if (applySub) { areAlphaEq(sub(half.head), target) } else { areAlphaEq(half.head, target) }
    //      if (found) {
    //        half.tail
    //      } else {
    //        Seq[E](half.head) ++ checkHalf(half.tail, target, sub, applySub)
    //      }
    //    }
    def filterHelper(e: E): Boolean = {
      areAlphaEq(sub(e), target)
    }

    val newSeq = if (applySub) {
      half.filter(!filterHelper(_))
    } else {
      half.filter(!areAlphaEq(_, target))
    }

    val diffs = half.diff(newSeq)
    //    println("targ: " + target)
    //    println("diffs: " + diffs)

    val subOut = if (diffs.size > 0) {
      val formula = diffs.head //should only be one //TODO: ensure this!
      //      println("form: " + formula)
      val renameSub = unify((formula, target) :: Nil)
      //      println(renameSub)
      renameSub.get //should never be empty
    } else {
      null
    }

    (newSeq.toList, subOut)
  }

}

abstract class FOAbstractRPIAlgorithm
  extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  protected def safeLiteralsFromChild(childWithSafeLiterals: (SequentProofNode, IClause),
    parent: SequentProofNode, edgesToDelete: FOEdgesToDelete) = {

    childWithSafeLiterals match {
      //in these cases, 'child' is the unifying resolution
      case (child @ UnifyingResolution(left, right, _, auxR), safeLiterals) if left == parent =>
        if (edgesToDelete.isMarked(child, right)) {
          println("using safe literals")
          safeLiterals
        } else {
          //          def mgu = child.asInstanceOf[UnifyingResolution].mgu
          //          def newAuxR = mgu(auxR)
          //          addLiteralSmart(safeLiterals, newAuxR, false, left, right)
          addLiteralSmart(safeLiterals, auxR, false, left, right)
        }

      case (child @ UnifyingResolution(left, right, auxL, _), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child, left)) {
          println("using safe B " + child)
          println(safeLiterals)
          safeLiterals
        } else {
          //          def mgu = child.asInstanceOf[UnifyingResolution].mgu
          //
          //          def nodeLeftClean = child.asInstanceOf[UnifyingResolution].leftClean
          //
          //          //maybe this stuff  isn't necessary--------
          //          //    println("left: " + left)
          //          //    println("cleanleft: " + nodeLeftClean)
          //          def getRenamedMGU(original: Sequent, clean: Sequent, sub: Substitution, vars: MSet[Var]): Substitution = {
          //            val renamingForward = findRenaming(original, clean)(vars)
          //            if (renamingForward.size == 0) {
          //              return sub
          //            }
          //
          //            val renamingBackward = findRenaming(clean, original)(vars)
          //
          //            println("GRM: forward: " + renamingForward)
          //            println("GRM: backward: " + renamingBackward)
          //
          //            def appSub(pair: (Var, E)): (Var, E) = {
          //              if (!renamingForward.get(pair._1).isEmpty) {
          //                (renamingForward(pair._1).asInstanceOf[Var], pair._2)
          //              } else if (!renamingBackward.get(pair._1).isEmpty) {
          //                (renamingBackward(pair._1).asInstanceOf[Var], pair._2)
          //              } else {
          //                pair
          //              }
          //
          //            }
          //
          //            val outPairs = sub.toList.map(p => appSub(p))
          //
          //            Substitution(outPairs: _*)
          //          }
          //          def vars = MSet[Var]() ++ getSetOfVars(left) ++ getSetOfVars(nodeLeftClean)
          //          val fixedMGU = getRenamedMGU(left.conclusion, nodeLeftClean.conclusion, mgu, vars)
          //          println("XXX mgu: " + mgu)
          //          println("XXX fixedMGU: " + fixedMGU)
          //          println("XXX auxL : " + auxL)
          //          //-------------------     
          //
          //          def newAuxL = mgu(auxL)
          //          addLiteralSmart(safeLiterals, newAuxL, true, left, right)
          addLiteralSmart(safeLiterals, auxL, true, left, right)

        }

      case (_, safeLiterals) => {
        println("child with safe literals: " + childWithSafeLiterals)
        safeLiterals
      }
      // Unchecked Inf case _ => throw new Exception("Unknown or impossible inference rule")
    }
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
    //TODO: change this to reflect changes above regarding what is considered safe?
    for (lit <- seqHalf) {
      unify((lit, aux) :: Nil)(uVars) match {
        case None => {}
        case Some(_) => {
          println("lit: " + lit + " and " + aux)
          return seq
        }
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

  protected def finalCheck(safeLit: Sequent, seqToDelete: Sequent): Boolean = {

    def checkHelperAlphaManualX(computed: Seq[E], desired: Seq[E])(implicit unifiableVariables: MSet[Var]): Boolean = {
      println("X check: " + computed)
      println("X check: " + desired)
      //      if (computed.size == 0 && desired.size == 0) {
      if (desired.size == 0) {
        return true
      }

      for (f <- computed) {

        for (g <- desired) {
          val u = unify((f, g) :: Nil)
          u match {
            case Some(s) => {
              if (checkSubstitutions(s)) {
                //add current subs to this (not checkSubs is used above! modify with care)
                return checkHelperAlphaManualX(computed.filter(!_.equals(f)), desired.filter(!_.equals(g)))
              }
            }
            case None => {
            }
          }
        }

      }
      false
    }

    def desiredFoundX(computed: Sequent, desired: Sequent)(implicit unifiableVariables: MSet[Var]): Boolean = {
      if (computed == desired) {
        return true
      } else {
        val commonVars = (getSetOfVars(Axiom(computed.ant)) intersect getSetOfVars(Axiom(computed.suc)))

        println("CVS: " + commonVars)

        def generateSubstitutionOptionsX(computed: Seq[E], desired: Seq[E]) = {
          val map = new MMap[Var, Set[E]]()
          for (c <- computed) {
            //            println("checking c: " + c)
            val cVars = getSetOfVars(c)
            for (d <- desired) {
              println("checking d: " + d)
              val dVars = getSetOfVars(d)

              val cAxiom = new Axiom(Sequent(c)())
              val dAxiom = new Axiom(Sequent(d)())
              val dAxiomClean = fixSharedNoFilter(dAxiom, cAxiom, 0, cVars union dVars)
              val dClean = dAxiomClean.conclusion.ant.head

              //should never not be able to unify -- one is the other, but with new variable names
              val dToCleanSub = (unify((d, dClean) :: Nil)(cVars union dVars)).get
              val inverseSubs = dToCleanSub.toMap[Var, E].map(_.swap)
              val inverseSubsCasted = convertTypes(inverseSubs.toList)
              val inverseSub = Substitution(inverseSubsCasted: _*)

              val u = unify((c, dClean) :: Nil)(cVars union dVars)

              u match {
                case Some(s) => {
                  println("matched with c: " + c)
                  //                  if (checkSubstitutions(s)) {
                  //make sure it's just a renaming

                  //so that var could have gone to any of the variables in d; add them all
                  //NO -- it can only go to what the sub said it could!
                  //                  println("A")
                  for (cv <- unifiableVariables) {

                    val sub = inverseSub(getValidSubstitution(s, cv))
                    val realVars = getSetOfVars(sub)
                    if (map.keySet.contains(cv)) {
                      //                      println("B")
                      //update that set
                      def sub = u.get
                      def entry = sub.get(cv)
                      map.put(cv, map.get(cv).get ++ entry)
                    } else {
                      //                      println("C")
                      //add a new set
                      //note the conversion is safe since checkSubstitutions already confirms it's a var
                      def sub = u.get
                      def entry = sub.get(cv)
                      map.put(cv, Set[Var]() ++ entry)
                    }

                  }

                  //                  }

                }
                case None => {
                }
              }

            }
          }
          map
        }

        def intersectMapsX(a: MMap[Var, Set[E]], b: MMap[Var, Set[E]]): MMap[Var, Set[E]] = {
          val out = MMap[Var, Set[E]]()

          val sharedKeys = (a.keySet).intersect(b.keySet)
          for (sKey <- sharedKeys) {
            out.put(sKey, a.get(sKey).get intersect b.get(sKey).get)
          }
          val aOnlyKeys = (a.keySet) -- sharedKeys
          for (aKey <- aOnlyKeys) {
            out.put(aKey, a.get(aKey).get)
          }
          val bOnlyKeys = (b.keySet) -- sharedKeys
          for (bKey <- bOnlyKeys) {
            out.put(bKey, b.get(bKey).get)
          }

          out
        }

        def validMapX(m: MMap[Var, Set[E]], vars: MSet[Var]): Boolean = {
          for (k <- m.keySet) {
            if (vars.contains(k) && m.get(k).get.size > 1) {
              return false
            }
            if (!vars.contains(k) && m.get(k).get.size == 0) {
              return false
            }
          }
          true
        }
        val antMap = generateSubstitutionOptionsX(computed.ant, desired.ant)
        if(getSetOfVars(desired.ant: _*).size > 0 && antMap.size == 0){
          return false
        }
        val sucMap = generateSubstitutionOptionsX(computed.suc, desired.suc)
        if(getSetOfVars(desired.suc: _*).size > 0 && sucMap.size == 0){
          return false
        }        
        println("ANT MAP: " + antMap)
        println("SUC MAP: " + sucMap)
        val intersectedMap = intersectMapsX(antMap, sucMap)

        println("INTERSECTION MAP: " + intersectedMap)
        println("INTERSECTION MAP: " + intersectedMap.size)

        if (!validMapX(intersectedMap, vars)) {
          return false
        }

        //        if (intersectedMap.size == 0 && unifiableVariables.size > 0) {
        //          return false
        //        }

        //        println("getting to alpha checks")
        //        if (checkHelperAlphaManualX(computed.ant.distinct, desired.ant.distinct)) {
        //          if (checkHelperAlphaManualX(computed.suc.distinct, desired.suc.distinct)) {
        //            return true
        //          }
        //        }
        //        false
        true
      }
    }

    def antVars = getSetOfVars(seqToDelete.ant: _*)
    def sucVars = getSetOfVars(seqToDelete.suc: _*)
    def antVarsB = getSetOfVars(safeLit.ant: _*)
    def sucVarsB = getSetOfVars(safeLit.suc: _*)
    def vars = MSet[Var]() ++ antVars ++ sucVars //++ antVarsB ++ sucVarsB
    println("IN FINAL: " + safeLit)
    println("     AND: " + seqToDelete)
    def safeLitB = Sequent(safeLit.suc: _*)(safeLit.ant: _*)
    println("IN FINAB: " + safeLitB)
    println("VARS: " + vars)
    desiredFoundX(safeLit, seqToDelete)(vars)
  }

  protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
    val edgesToDelete = new FOEdgesToDelete()
    var auxMap = new MMap[SequentProofNode, E]()
    var mguMap = new MMap[SequentProofNode, Substitution]()
    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      println("SAFE LITERALS for " + p + " => " + safeLiterals)
      p match {
        //        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.suc, auxL)) => {
        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.suc, auxL)
          && checkForResSmartLeft(safeLiterals.suc, auxL, p) && finalCheck(safeLiterals.toSeqSequent, left.conclusion)) => {
          //&&  finalCheck(p.conclusion, right.conclusion)
          //          println("p: " + p + " and right: " + right + " edge marked")
          //          println("other edge: " +  left + " and mgu " + p.asInstanceOf[UnifyingResolution].mgu)
          //          println("p, auxL: " + p + "   " + auxL)
          auxMap.put(p, auxL)
          mguMap.put(p, p.asInstanceOf[UnifyingResolution].mgu)
          println("marked b] " + p + " AND " + right)
          println("auxL: " + auxL)
          println("mgu (p): " + p.asInstanceOf[UnifyingResolution].mgu)
          //          println("omg?????: " + finalCheck(p.conclusion, right.conclusion))
          edgesToDelete.markRightEdge(p)
        }
        //        case UnifyingResolution(left, right, auxL, auxR) if checkForRes(safeLiterals.ant, auxR) => {
        //TODO: use only the latter function
        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.ant, auxR) &&
          checkForResSmartRight(safeLiterals.ant, auxR, p) && finalCheck(safeLiterals.toSeqSequent, right.conclusion)) => {
          // && finalCheck(p.conclusion, left.conclusion)               
          //          println("p: " + p + " and right: " + left + " edge marked")
          //          println("other edge: " + right + " and mgu " + p.asInstanceOf[UnifyingResolution].mgu)                    
          println("marked a] " + p + " AND  " + left)
          println("auxR: " + auxR)
          println(" and mgu " + p.asInstanceOf[UnifyingResolution].mgu)

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
