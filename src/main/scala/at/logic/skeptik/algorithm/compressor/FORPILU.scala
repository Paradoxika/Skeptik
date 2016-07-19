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

	//(jgorzny) 2 June 2015:
	//This checks the aux after the original mgu was applied
	//prevents some terrible attempts to lower
	//NOTE: p MUST be a unifying resolution node
	protected def checkForResSmart(safeLiteralsHalf: Set[E], aux: E, p: SequentProofNode): Boolean = {

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
							//										val sub = mrr.asInstanceOf[UnifyingResolution].mgu
							//							mguMap.put(p, sub)
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

				case UnifyingResolution(left, right, pivot, _) if (findRenaming(fixedLeft.conclusion, p.conclusion)(unifiableVariables) != null) => {
					//If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
					//the fixed parent; so the pivot better be missing.
					assert(!checkForRes(fixedLeft.conclusion.toSetSequent.suc, pivot))
					fixedLeft
				}
				case UnifyingResolution(left, right, _, pivot) if (findRenaming(fixedRight.conclusion, p.conclusion)(unifiableVariables) != null) => {
					//If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
					//the fixed parent; so the pivot better be missing.
					assert(!checkForRes(fixedLeft.conclusion.toSetSequent.ant, pivot))
					fixedRight
				}

				// Main case (rebuild a resolution)
				case UnifyingResolution(left, right, auxL, auxR) => { 

					val nonEmptyLeftMap = !auxMap.get(left).isEmpty && !mguMap.get(left).isEmpty
							val nonEmptyRightMap = !auxMap.get(right).isEmpty && !mguMap.get(right).isEmpty

							val ambiguousErrorString = "Resolution (MRR): the resolvent is ambiguous."

							//We may have to apply a FO sub
							def newFixedRight = if (!mguMap.get(fixedRight).isEmpty) {
								new FOSubstitution(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
							} else {
								fixedRight
							}

					def newFixedLeft = if (!mguMap.get(fixedLeft).isEmpty) {
						new FOSubstitution(fixedLeft, mguMap.get(fixedLeft).get)(unifiableVariables)
					} else {
						fixedLeft
					}					

					try {

						UnifyingResolutionMRR(fixedRight, fixedLeft)(unifiableVariables)

					} catch {
					case e: Exception => {
						if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) {
							if (nonEmptyLeftMap && !nonEmptyRightMap) {
								val oldMGU = mguMap.get(left).get
										fixAmbiguous(fixedLeft, newFixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
							} else {
								val oldMGU = mguMap.get(right).get
										fixAmbiguous(newFixedLeft, fixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
							}
						} else {

							val oldMGU = if (mguMap.get(left).isEmpty) { Substitution() } else { mguMap.get(left).get }


							try {
								attemptGreedyContraction(fixedLeft, fixedRight, newFixedRight, ambiguousErrorString, left, right, auxL, auxR, mguMap)(unifiableVariables)
							} catch {
							case omg: Exception => {
								val t = fixAmbiguousB(fixedLeft, fixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
										t
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

	def attemptGreedyContraction(fixedLeft: SequentProofNode, fixedRight: SequentProofNode, newFixedRight: SequentProofNode, 
			ambiguousErrorString: String, left: SequentProofNode, right: SequentProofNode, auxL: E, auxR: E, 
			mguMap: MMap[SequentProofNode, Substitution])(implicit unifiableVariables: MSet[Var]) = {

		try {

			UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables)
		} catch {
		case e: Exception if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) => {

			try {
				UnifyingResolutionMRR(fixedLeft, Contraction(fixedRight)(unifiableVariables))(unifiableVariables)
			} catch {
			case f: Exception => {

				val oldMGU = if (mguMap.get(left).isEmpty) { Substitution() } else { mguMap.get(left).get }
				fixAmbiguous(fixedLeft, fixedRight, oldMGU, left, right, auxL, auxR)(unifiableVariables)
			}
			}
		}
		case e: Exception => {
			throw new Exception("FORPI Failed!")
		}
		}
	}
	//24June2016
	def fixAmbiguousB(fLeft: SequentProofNode, fRight: SequentProofNode, oldMGU: Substitution, left: SequentProofNode, right: SequentProofNode, auxL: E, auxR: E)(implicit unifiableVariables: MSet[Var]) = {
		var desired = Sequent()()
				val fRightC = if(Contraction(fRight)(unifiableVariables).conclusion.size < fRight.conclusion.size) { Contraction(fRight)(unifiableVariables) } else { fRight }
		val fLeftCon = if(Contraction(fLeft)(unifiableVariables).conclusion.size < fLeft.conclusion.size) { Contraction(fLeft)(unifiableVariables) } else { fLeft }
		val fLeftC = fixSharedNoFilter(fLeftCon,fRightC,0, unifiableVariables)

				for(ls <- fLeftC.conclusion.suc){
					unify((ls, auxL):: Nil)(unifiableVariables) match {
					case Some(_) => { //something 
					  //Don't add to the remainder
					}
					case None =>{
						desired = desired + ls
					}
					}
				}

		for(la <- fLeftC.conclusion.ant){
			desired = la +: desired
		}

		for(ra <- fRightC.conclusion.ant){
			unify((ra, auxR):: Nil)(unifiableVariables) match {
			case Some(_) => { //something }

			}
			case None =>{
				desired = ra +: desired 
			}
			}
		}	  

		for(rs <- fRightC.conclusion.suc){
			desired =   desired + rs
		}	  
		val outval = try{
			val out = UnifyingResolution(fLeftC, fRightC, desired)(unifiableVariables)
					out
		} catch {
		case _=> {
			val outB = UnifyingResolution(fRightC, fLeftC, desired)(unifiableVariables)
			outB
		}
		}
		val outC = if(Contraction(outval)(unifiableVariables).conclusion.size < outval.conclusion.size) { Contraction(outval)(unifiableVariables) } else { outval }
		outC
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
		val (leftRemainder, leftSub) = findRemainder(fLeftClean, auxL, oldMGU, leftEq, true)
				val fRightClean = if (!fRight.equals(right)) {
					new FOSubstitution(fRight, oldMGU).conclusion
				} else {
					fRight.conclusion
				}
		val (rightRemainder, rightSub) = findRemainder(fRightClean, auxR, oldMGU, rightEq, false)
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

	def findRemainder(seq: Sequent, target: E, mgu: Substitution, applySub: Boolean, removeFromAnt: Boolean)(implicit unifiableVariables: MSet[Var]): (Sequent, Substitution) = {	  
		val (newAnt, antSub) = if (removeFromAnt) { checkHalf(seq.ant, target, mgu, applySub) } else { (seq.ant.toList, null) }
		val (newSuc, sucSub) = if (!removeFromAnt) { checkHalf(seq.suc, target, mgu, applySub) } else { (seq.suc.toList, null) }

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
					val formula = diffs.head //should only be one

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

		for (lit <- seqHalf) {
			unify((lit, aux) :: Nil)(uVars) match {
			case None => {}
			case Some(_) => {
				return seq
			}
			}
		}

		//24 June 2015
		//see if aux shares a variable with something in the safe; if so, change it to avoid creating dependencies
		val newAuxNode = fixSharedNoFilter(Axiom(Sequent(aux)()), Axiom(seq.toSeqSequent), 0, uVars)
				val newAux = newAuxNode.conclusion.ant.head
				//val newAux = aux
				//---

				def out = if (addToAntecedent) {
					(newAux +: seq)
				} else {
					(seq + newAux)
				}
		out
	}

	protected def computeSafeLiterals(proof: SequentProofNode,
			childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
			edgesToDelete: FOEdgesToDelete): IClause

}

trait FOCollectEdgesUsingSafeLiterals
extends FOAbstractRPIAlgorithm with FindDesiredSequent {

	//ensure that the node that will be replacing the unifying resolution is entirely safe
	protected def finalCheck(safeLit: Sequent, seqToDelete: Sequent): Boolean = {


			def desiredIsContained(computed: Sequent, desired: Sequent)(implicit unifiableVariables: MSet[Var]): Boolean = {
				if (computed == desired) {
					return true
				} else {
					
				  val dVars = getSetOfVars(desired.ant: _*) union getSetOfVars(desired.suc: _*)
				  
				  val cVars = getSetOfVars(computed.ant: _*) union getSetOfVars(computed.suc: _*)
				  
				  
					val antMap = generateSubstitutionOptions(computed.ant, desired.ant, cVars)
							if (getSetOfVars(computed.ant: _*).size > 0 && antMap.size == 0) {
								return false
							}

					val sucMap = generateSubstitutionOptions(computed.suc, desired.suc, cVars)
							if (getSetOfVars(computed.suc: _*).size > 0 && sucMap.size == 0) {
								return false
							}
					val intersectedMap = intersectMaps(antMap, sucMap)
					  if (!validMap(intersectedMap, cVars)) {

								return checkInvalidMap(intersectedMap, cVars, computed, desired)// false
							}
					if (!checkMapSub(intersectedMap, cVars, computed, desired)){
					  return false
					}
					true
				}
			}

			def antVars = getSetOfVars(seqToDelete.ant: _*)
					def sucVars = getSetOfVars(seqToDelete.suc: _*)
					def antVarsB = getSetOfVars(safeLit.ant: _*)
					def sucVarsB = getSetOfVars(safeLit.suc: _*)
					
					def allvars = MSet[Var]() ++ antVars ++ sucVars ++ antVarsB ++ sucVarsB
					def safeClean = fixSharedNoFilter(Axiom(safeLit), Axiom(seqToDelete), 0, allvars)

					def antVarsC = getSetOfVars(safeClean.conclusion.ant: _*)
					def sucVarsC = getSetOfVars(safeClean.conclusion.suc: _*)
					def allvarsC = MSet[Var]() ++ antVars ++ sucVars ++ antVarsB ++ sucVarsB ++ antVarsC ++ sucVarsC

					desiredIsContained(safeClean.conclusion, seqToDelete)(allvarsC)

	}

	//TODO: rename helper function names
	protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
		val edgesToDelete = new FOEdgesToDelete()
		var auxMap = new MMap[SequentProofNode, E]()
		var mguMap = new MMap[SequentProofNode, Substitution]()
		def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
			val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
					p match {
					case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.suc, auxL)
							&& checkForResSmart(safeLiterals.suc, auxL, p) && finalCheck(left.conclusion, safeLiterals.toSeqSequent )) => {
								auxMap.put(p, auxL)
								mguMap.put(p, p.asInstanceOf[UnifyingResolution].mgu)
								edgesToDelete.markRightEdge(p)
							}
					case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.ant, auxR) &&
							checkForResSmart(safeLiterals.ant, auxR, p) && finalCheck(right.conclusion, safeLiterals.toSeqSequent )) => {
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
				smartIntersect(acc,safeLiteralsFromChild(v, proof, edgesToDelete))
			}
			}
			}
	}

	protected def smartIntersect(l: IClause, r: IClause) = {
		var out = Sequent()() 
				val uVars = getSetOfVars(Axiom(l.toSeqSequent)) union getSetOfVars(Axiom(r.toSeqSequent))
				for(la <- l.ant){
					for(ra <- r.ant){
						unify((la, ra) :: Nil)(uVars) match {
						case None => {}
						case Some(sub) => {
						  val newLA = getCleanLiteral(la, sub, out)						  
							out =  newLA +: out
						}
						}
					}
				}

		for(ls <- l.suc){
			for(rs <- r.suc){
				unify((ls, rs) :: Nil)(uVars) match {
				case None => {}
				case Some(sub) => {
				  val newLS = getCleanLiteral(ls, sub, out)					  
					out =  out + newLS
				}
				}
			}
		}

		out.toSetSequent

	}
	
	def getCleanLiteral(l: E, s:Substitution, rest: Sequent) ={
	  val restAx = Axiom(rest)
	  val lsubbed = s(l)
	  val lsAx = Axiom(Sequent(lsubbed)())
	  val vars = getSetOfVars(restAx) union getSetOfVars(lsAx)

	  
	  val lsAxClean = fixSharedNoFilter(lsAx,restAx,0, vars)
	  
	  val cleanL = lsAxClean.conclusion.ant.head
	  
	  cleanL
	}

}
