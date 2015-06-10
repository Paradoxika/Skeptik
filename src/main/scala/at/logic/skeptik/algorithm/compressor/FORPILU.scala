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

    for (safeLit <- safeLiteralsHalf) {
      val uvars = (getSetOfVars(newAux) union getSetOfVars(safeLit))
      val uvarsB = getMSet(uvars)
      val isMore = isMoreGeneral(Sequent(newAux)(), Sequent(safeLit)())(uvarsB)
      unify((newAux, safeLit) :: Nil)(getSetOfVars(newAux)) match {
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

    def newAux = oldMGU(aux) 

    for (safeLit <- safeLiteralsHalf) {
      val uvars = (getSetOfVars(newAux) union getSetOfVars(safeLit))
      val uvarsB = getMSet(uvars)
      val isMore = isMoreGeneral(Sequent(newAux)(), Sequent(safeLit)())(uvarsB)
      unify((newAux, safeLit) :: Nil)(getSetOfVars(newAux)) match {
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
        val sub = p.asInstanceOf[UnifyingResolution].mgu
        mguMap.put(fixedRight, sub)
        fixedRight
      }
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, right) => {
        val sub = p.asInstanceOf[UnifyingResolution].mgu
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
        //TODO: use map for lookup, find carry, and build new expected result, use that to fix ambiguity
        //   --- necessary now? 

        val nonEmptyLeftMap = !auxMap.get(left).isEmpty && !mguMap.get(left).isEmpty
        val nonEmptyRightMap = !auxMap.get(right).isEmpty && !mguMap.get(right).isEmpty

        val ambiguousErrorString = "Resolution (MRR): the resolvent is ambiguous."

        //TODO: clean this up?
        try {
          def newFixedRight = if (!mguMap.get(fixedRight).isEmpty) {
            new FOSubstitution(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
          } else {
            fixedRight
          }
          def attemptD = UnifyingResolutionMRR(newFixedRight, fixedLeft)(unifiableVariables)
          attemptD
        } catch {
          case e: Exception => {
            if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) {
              if (nonEmptyLeftMap && !nonEmptyRightMap) {
                val oldMGU = mguMap.get(left).get
                def newFixedRight = if (!mguMap.get(fixedRight).isEmpty) {
                  new FOSubstitution(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
                } else {
                  fixedRight
                }
                def attemptC = fixAmbiguous(fixedLeft, newFixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
                attemptC
              } else {
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
                def attemptB = UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables)
                attemptB
              } catch {
                case e: Exception if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) => {

                  try {
                    def attempt = UnifyingResolutionMRR(fixedLeft, Contraction(fixedRight)(unifiableVariables))(unifiableVariables)
                    attempt
                  } catch {
                    case f: Exception => {
                      val oldMGU = mguMap.get(left).get
                      def nonAmbig = fixAmbiguous(fixedLeft, fixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
                      nonAmbig
                    }
                  }
                }
                case e: Exception => {
                  throw new Exception("FORPI Failed!")
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
    val fRightClean = if (!fRight.equals(right)) {
      new FOSubstitution(fRight, oldMGU).conclusion
    } else {
      fRight.conclusion
    }
    val (rightRemainder, rightSub) = findRemainder(fRightClean, auxR, oldMGU, rightEq)

    //TODO: this for the left? 
    //TODO: do this conditionally only?
    val rightRemainderWithNewMGU = (new FOSubstitution(Axiom(rightRemainder), newMGU)).conclusion

    val tempLeft = new FOSubstitution(new FOSubstitution(Axiom(leftRemainder), leftSub), newMGU)
    val tempRight = Axiom(rightRemainderWithNewMGU)
    val cleanLeftRemainder = fixSharedNoFilter(tempLeft, tempRight, 0, unifiableVariables).conclusion

    val newTarget = rightRemainderWithNewMGU.union(tempLeft.conclusion)

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
    def filterHelper(e: E): Boolean = {
      areAlphaEq(sub(e), target)
    }

    val newSeq = if (applySub) {
      half.filter(!filterHelper(_))
    } else {
      half.filter(!areAlphaEq(_, target))
    }

    val diffs = half.diff(newSeq)

    val subOut = if (diffs.size > 0) {
      val formula = diffs.head //should only be one //TODO: ensure this!
      val renameSub = unify((formula, target) :: Nil)
      renameSub.get //should never be empty
    } else {
      null
    }

    (newSeq.toList, subOut)
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
      case (child @ UnifyingResolution(left, right, _, auxR), safeLiterals) if left == parent =>
        if (edgesToDelete.isMarked(child, right)) {
          safeLiterals
        } else {
          def auxRb = findActualAux(left.conclusion.suc, auxR, child.asInstanceOf[UnifyingResolution].mgu)
          addLiteralSmart(safeLiterals, auxRb, false, left, right)
        }

      case (child @ UnifyingResolution(left, right, auxL, _), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child, left)) {
          safeLiterals
        } else {
          def auxLb = findActualAux(right.conclusion.ant, auxL, child.asInstanceOf[UnifyingResolution].mgu)
          addLiteralSmart(safeLiterals, auxL, true, left, right)
        }

      case (p, safeLiterals) => {
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
  extends FOAbstractRPIAlgorithm {

  //ensure that the node that will be replacing the unifying resolution is entirely safe
  protected def finalCheck(safeLit: Sequent, seqToDelete: Sequent): Boolean = {

    def checkHelperAlphaManualX(computed: Seq[E], desired: Seq[E])(implicit unifiableVariables: MSet[Var]): Boolean = {
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
        
        def generateSubstitutionOptionsX(computed: Seq[E], desired: Seq[E], vs: MSet[Var]) = {
          val map = new MMap[Var, Set[E]]()
          for (c <- computed) {
            val cVars = getSetOfVars(c)
            for (d <- desired) {
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

              val u = unify((dClean, c) :: Nil)(vs)

              u match {
                case Some(s) => {
                  //so that var could have gone to any of the variables in d; add them all
                  //NO -- it can only go to what the sub said it could!
                  for (cv <- unifiableVariables) {

                    val sub = inverseSub(getValidSubstitution(s, cv))
                    val realVars = getSetOfVars(sub)
                    if (map.keySet.contains(cv)) {
                      //update that set
                      def sub = u.get
                      def entry = sub.get(cv)
                      if (!entry.isEmpty) {
                        map.put(cv, map.get(cv).get ++ entry)
                      }
                    } else {
                      //add a new set
                      //note the conversion is safe since checkSubstitutions already confirms it's a var
                      def sub = u.get
                      def entry = sub.get(cv)
                      if (!entry.isEmpty) {
                        map.put(cv, Set[Var]() ++ entry)
                      }
                    }

                  }

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
        val antMap = generateSubstitutionOptionsX(computed.ant, desired.ant, unifiableVariables)
        if (getSetOfVars(desired.ant: _*).size > 0 && antMap.size == 0) {
          return false
        }
        val sucMap = generateSubstitutionOptionsX(computed.suc, desired.suc, unifiableVariables)
        if (getSetOfVars(desired.suc: _*).size > 0 && sucMap.size == 0) {
          return false
        }
        val intersectedMap = intersectMapsX(antMap, sucMap)

        if (!validMapX(intersectedMap, vars)) {
          return false
        }

        def findFromMap(m: MMap[Var, Set[E]], vars: MSet[Var]): Boolean = {
          val subList = MSet[(Var, E)]()

          for (k <- m.keySet) {
            if (m.get(k).get.size > 0) {
              subList.add((k, m.get(k).get.head))
            }
          }

          val sub = Substitution(subList.toSeq: _*)
          def foundExactly(target: Seq[E], source: Seq[E]): Boolean = {
            if (target.size == 0) {
              return true
            }
            target match {
              case h :: t => {
                for (s <- source) {
                  if (h.equals(s)) {
                    return foundExactly(t, source)
                  }
                }
              }
            }

            false
          }

          val newDesiredAnt = (desired.ant).map(e => sub(e))

          val newDesiredSuc = (desired.suc).map(e => sub(e))
          foundExactly(newDesiredAnt, computed.ant) && foundExactly(newDesiredSuc, computed.suc)
        }

        if (!findFromMap(intersectedMap, vars)) {
          return false
        }

        true
      }
    }

    def antVars = getSetOfVars(seqToDelete.ant: _*)
    def sucVars = getSetOfVars(seqToDelete.suc: _*)
    def antVarsB = getSetOfVars(safeLit.ant: _*)
    def sucVarsB = getSetOfVars(safeLit.suc: _*)
    def vars = MSet[Var]() ++ antVars ++ sucVars 
    def allvars = MSet[Var]() ++ antVars ++ sucVars ++ antVarsB ++ sucVarsB

    def safeClean = fixSharedNoFilter(Axiom(safeLit), Axiom(seqToDelete), 0, allvars)

    desiredFoundX(safeClean.conclusion, seqToDelete)(vars)

  }

  protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
    val edgesToDelete = new FOEdgesToDelete()
    var auxMap = new MMap[SequentProofNode, E]()
    var mguMap = new MMap[SequentProofNode, Substitution]()
    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      p match {
        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.suc, auxL)
          && checkForResSmartLeft(safeLiterals.suc, auxL, p) && finalCheck(safeLiterals.toSeqSequent, left.conclusion)) => {
          auxMap.put(p, auxL)
          mguMap.put(p, p.asInstanceOf[UnifyingResolution].mgu)
          edgesToDelete.markRightEdge(p)
        }
        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.ant, auxR) &&
          checkForResSmartRight(safeLiterals.ant, auxR, p) && finalCheck(safeLiterals.toSeqSequent, right.conclusion)) => {
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
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) =>
          {
            acc intersect safeLiteralsFromChild(v, proof, edgesToDelete)
          }
        }
    }
  }
}
