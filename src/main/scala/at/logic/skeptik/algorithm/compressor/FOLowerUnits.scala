package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.MRRException
import at.logic.skeptik.proof.sequent.resolution.Contraction
import at.logic.skeptik.proof.sequent.resolution.CanRenameVariables
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.proof.sequent.resolution.FindMGU

import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import collection.mutable.{ Queue, HashMap => MMap }
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.expression._
import collection.mutable.{ HashSet => MSet }
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents
import at.logic.skeptik.expression.substitution.immutable.Substitution

/*
 * Description of fix for tracking issue, e.g. SET824-2.spass
 * 
 * Implement this fix from Bruno on the Google-Dev Group for Skeptik
 * 
 * I see. In principle, the ideal solution for all problems related to not knowing what to contract is to keep track of the descendants of formulas that were originally resolved away by the unit.  For example:

Let's say we had

C1 =  "F1, F2 |-"
C2 =  "G1, G2 |-"
U   =  " |- H"

with the unit U being resolved with C1 (on formula F1) and C2 (on formula G1).

And now suppose we would like to lower U.

When reintroducing U in the bottom of the proof, we will have to resolve it with a root clause R of the form:

" Gamma, F1', G1' |- Delta"    (where Gamma and Delta are lists of formulas and F1' and G1' are descendants of, respectively, F1 and G1).

Now, instead of searching for a good contraction that would merge some (or most) formulas in "Gamma, F1', G1' ", we should know that we have to contract exactly F1' with G1'.

Of course, this is not easy to implement, because the descendants change due to unifications.

One possible way to implement this is to have a hashmap M, mapping every unit that has been lowered to a list of (descendants of) auxiliary formulas of the clauses that were originally resolved against the unit. The difficulty is that M would have to be updated. For example, originally M would be mapping U to {F1, G1}; but as we go down in the proof, M would have to be progressively updated so that U is mapped to {F1', G1'}.  If implemented in a naive way, this update would be costly, because, for every resolution step, we would have to traverse M, in order to find which key-value pairs need to be updated. To avoid this cost, an inverse HashMap N (now from formulas to units) could be created. Then, for example, when processing a resolution step that changes the formula F1 to F1', we could query N, which would tell us that F1 is mapped to U. Now we know that the pair (U, F1) in M has to be updated to (U, F1'). Likewise, (F1, U) in N has to be updated to (F1', U).



I'm afraid that, unless we do this careful tracking of descendants in order to contract correctly, there will always be cases on which the algorithm will fail.

Nevertheless, if our current method of doing contractions (i.e. trying to find the right contraction somehow) works for the majority of cases, we can still use it as a good and "cheaper" approximation. And on the cases on which it fails, we simply return the original uncompressed proof. Not all algorithms need to accept all inputs.

 * 
 * 
 */

object FOLowerUnits
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with CanRenameVariables with FindDesiredSequent with FindMGU {

	def isUnitClause(s: Sequent) = s.ant.length + s.suc.length == 1

			// ToDo: optimize this by interlacing collectUnits and fixProofNodes

			def cleanUpLists(in: IndexedSeq[Seq[Seq[E]]]) = {
		var out = List[E]()
				for (outer <- in) {
					for (inner <- outer) {
						out = out ++ inner
					}
				}
		out.distinct
	}

	def getUnitLiteralUsingAux(p: SequentProofNode, u: SequentProofNode, node: SequentProofNode, vars: MSet[Var]) = {

		val cleanMGU = if (!node.asInstanceOf[UnifyingResolution].leftPremise.equals(u)) {
			val newVars = vars union getSetOfVars(node.asInstanceOf[UnifyingResolution].leftClean)
					findRenaming(node.asInstanceOf[UnifyingResolution].leftClean.conclusion,
							node.asInstanceOf[UnifyingResolution].leftPremise.conclusion)(newVars)

		} else {
			Substitution()
		}


		if (u.conclusion.ant.size > 0) {
			cleanMGU(node.asInstanceOf[UnifyingResolution].auxL)
		} else {
			node.asInstanceOf[UnifyingResolution].auxR
		}
	}

	def getAuxVars(listOfUnits: List[E]) = {
		val out = MSet[Var]()
				for (e <- listOfUnits) {
					val eVars = getSetOfVars(e)
							for (v <- eVars) {
								out.add(v)
							}
				}
		out
	}

	def collectUnits(proof: Proof[SequentProofNode]) = {
		val vars = MSet[Var]()
				val unitsList = (proof :\ (Nil: List[SequentProofNode])) { (node, acc) =>
				if (isUnitClause(node.conclusion) && proof.childrenOf(node).length > 1) {
					val children = proof.childrenOf(node)

							//This gets the child of the unit, but really we want the other parent of the child of the unit.
							//so we do the following:
							val childrensParentsConclusionsSeqSeq = for (c <- children) yield {
								val parentsConclusions = for (p <- c.premises) yield {
									//Picks out (all) u_k in c_k
									val oo = getUnitLiteralUsingAux(p, node, c, vars)
											Seq[E](oo)
								}
								val varsC = getSetOfVars(c)
										for (v <- varsC) {
											vars += v
										}
								parentsConclusions.filter(_.length > 0)
							}


					val listOfUnits = cleanUpLists(childrensParentsConclusionsSeqSeq)

							val varsN = getSetOfVars(node)
							for (v <- varsN) {
								vars += v
							}

					val auxVars = getAuxVars(listOfUnits)
							for (v <- auxVars) {
								vars += v
							}

					if (checkListUnif(listOfUnits, vars)) {
						if (checkContraction(listOfUnits, vars, node)) {
							node :: acc
						} else {
							acc
						}
					} else {
						acc
					}

				} else {
					val varsN = getSetOfVars(node)
							for (v <- varsN) {
								vars += v
							}
					acc
				}
		}
		(unitsList, vars)
	}

	def checkContraction(listOfUnits: List[E], vars: MSet[Var], node: SequentProofNode): Boolean = {
		val newSeq = addAntecedents(listOfUnits)

				val con = try {
					Contraction(Axiom(newSeq))(vars)
				} catch {
				case e: Exception => {
					null
				}
				}

		if (con == null) {
			return false
		}

		val unitFormula = if (node.conclusion.ant.size > 0) {
			node.conclusion.ant.head
		} else {
			node.conclusion.suc.head
		}

		for (conForm <- con.conclusion.ant) {

			if (!isUnifiable((conForm, unitFormula))(vars)) {
				return false
			}
		}

		true
	}


	def checkListUnif(l: List[E], vars: MSet[Var]): Boolean = {
		if (l.length > 1) {
			val first = l.head
					val second = l.tail.head

					def isUnifiableWrapper(p: (E, E)) = {
				isUnifiable(p)(vars)
			}

			val mguResult = isUnifiable(first, second)(vars)

					if (mguResult) {
						checkListUnif(l.tail, vars)
					} else {
						false
					}
		} else if (l.length == 0) {
			//found no pair-wise unifiable list, so we don't lower this unit.
			false
		} else {
			true
		}
	}

	def childrenOfFixed(proof: Proof[SequentProofNode], node: SequentProofNode, vars: MSet[Var]): IndexedSeq[SequentProofNode] = {
		if (proof.childrenOf.contains(node)) {
			proof.childrenOf.get(node).get
		} else {
			for (n <- proof) {
				if (findRenaming(n.conclusion, node.conclusion)(vars) != null) {
					return proof.childrenOf.get(n).get
				}
			}
			IndexedSeq[SequentProofNode]()
		}
	}

	def tryReversingArguments(l: SequentProofNode, r: SequentProofNode, goal: Sequent, vars: MSet[Var]) = {
		try {
			UnifyingResolutionMRR(r, l, goal)(vars)
		} catch {
		case e: Exception => {
			//Do nothing
			null
		}
		}
	}

	def updateCarry(oldCarry: Sequent, sub: Substitution): Sequent = {
		if (oldCarry == null) {
			return null.asInstanceOf[Sequent]
		}
		val updatedCarry = if (sub != null) {
			val updatedAnt = if (oldCarry.ant != null) {
				oldCarry.ant.map(e => sub(e)).toList
			} else {
				List[E]()
			}
			val updatedSuc = if (oldCarry.suc != null) {
				oldCarry.suc.map(e => sub(e)).toList
			} else {
				List[E]()
			}
			addAntecedents(updatedAnt) union addSuccedents(updatedSuc)
		} else {
			oldCarry
		}
		updatedCarry
	}


	def addToMap(k: SequentProofNode, carry: Sequent, carryMap: MMap[SequentProofNode, Sequent]) = {
		if (carryMap.get(k).isEmpty) {
			carryMap.put(k, carry)
		} else {
			val existingCarry = carryMap.get(k).get
					if (existingCarry != null) {
						val bothCarries = existingCarry union carry
								carryMap.update(k, bothCarries)
					} else {
						carryMap.put(k, carry)
					}
		}
	}

	def addCarryToMapList(k: SequentProofNode, carry: Sequent, carryMapList: MMap[SequentProofNode, List[Sequent]]) = {
		if (carryMapList.get(k).isEmpty) {
			carryMapList.put(k, List[Sequent](carry))
		} else {
			val existingCarry = carryMapList.get(k).get
					val bothCarries = existingCarry ++ List[Sequent](carry)
					carryMapList.update(k, bothCarries)
		}
	}
	def fixProofNodes(unitsSet: Set[SequentProofNode], proof: Proof[SequentProofNode], vars: MSet[Var]) = {

		val fixMap = MMap[SequentProofNode, SequentProofNode]()

				val carryMap = MMap[SequentProofNode, Sequent]()

				val carryMapList = MMap[SequentProofNode, List[Sequent]]()
				val mguMap = MMap[SequentProofNode, Substitution]()




				def visit(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
			lazy val fixedLeft = fixedPremises.head;
			lazy val fixedRight = fixedPremises.last;


			val fixedP = node match {
			case Axiom(conclusion) => node
			case UnifyingResolution(left, right, _, _) if unitsSet contains left => {

				addToMap(fixedRight, makeUnitSequent(left, node.asInstanceOf[UnifyingResolution].auxR), carryMap)

				addCarryToMapList(fixedRight, makeUnitSequent(left, node.asInstanceOf[UnifyingResolution].auxR), carryMapList)
				val nodeMGU = node.asInstanceOf[UnifyingResolution].mgu
				mguMap.update(fixedRight, nodeMGU)
				fixedRight
			}
			case UnifyingResolution(left, right, _, _) if unitsSet contains right => {
				val nodeLeftClean = node.asInstanceOf[UnifyingResolution].leftClean

						val renamingBackward = findRenaming(nodeLeftClean.conclusion, left.conclusion)(vars)

						val auxLCarry = makeUnitSequent(right, node.asInstanceOf[UnifyingResolution].auxL)

						val fixedCarry = updateCarry(auxLCarry, renamingBackward)

						addToMap(fixedLeft, fixedCarry, carryMap)
						addCarryToMapList(fixedLeft, fixedCarry, carryMapList)
						val nodeMGU = node.asInstanceOf[UnifyingResolution].mgu

						val fixedMGU = getRenamedMGU(left.conclusion, nodeLeftClean.conclusion, nodeMGU, vars)

						mguMap.update(fixedLeft, fixedMGU)

						fixedLeft
			}
			//Need MRR since we might have to contract, in order to avoid ambiguous resolution
			case UnifyingResolution(left, right, _, _) => {

				try {
				  /*
				   * No need to update carry maps in this case as we're re-creating a resolution that exists (exactly)
				   * in the original proof. So nothing should be carried forward (as carried literals only exist during
				   * proof compression)
				   * 
				   */
				  val outMRR = if (fixedLeft.equals(left) && fixedRight.equals(right)) {
						val outMRRa = UnifyingResolutionMRR(fixedLeft, fixedRight, node.conclusion)(vars)
								mguMap.update(outMRRa, node.asInstanceOf[UnifyingResolution].mgu)
								outMRRa
					} else {
						findOriginalResolvent(fixedRight, fixedLeft, right, left, mguMap, vars, carryMap, carryMapList)
					}

					outMRR
				} catch {
				case e: Exception => {
					if (e.getMessage != null) {
						if (e.getMessage.equals("Resolution (MRR): the resolvent is ambiguous.")) {

							if (findRenaming(fixedLeft.conclusion, left.conclusion)(vars) != null &&
									findRenaming(fixedRight.conclusion, right.conclusion)(vars) != null) {
								return UnifyingResolutionMRR(fixedLeft, fixedRight, node.conclusion)(vars)
							}

              resolveUsingMultipleCarriedSubs(node, fixedRight, fixedLeft, right, left, mguMap, vars, carryMap, carryMapList)


						} else {
							UnifyingResolutionMRR(fixedRight, fixedLeft)(vars)
						}
					} else {
						throw new Exception("Compression failed! B")
					}
				}
				}
			}
			case Contraction(_, _) => {
				//For contractions, we pick a fixed node (but both are equal, so either works)
				//the fixed node is the same as the contraction syntactically, but has
				//the correct premise node in the fixed proof
				assert(fixedLeft == fixedRight)
				fixedRight
			}
			case _ => {
				node
			}
			}
			if (node == proof.root || unitsSet.contains(node)) {
				fixMap.update(node, fixedP)
			}
			fixedP
		}
		proof.foldDown(visit)
		fixMap
	}

	def unionSequents(a: Sequent, b: Sequent): Sequent = {
		if (a != null && b != null) {
			a.union(b)
		} else if (a != null && b == null) {
			a
		} else if (a == null && b != null) {
			b
		} else {
			null
		}
	}

	def getCarries(fixedRight: SequentProofNode, fixedLeft: SequentProofNode, right: SequentProofNode, left: SequentProofNode, carryMap: MMap[SequentProofNode, Sequent]) = {
		val carryA = if (!carryMap.get(fixedRight).isEmpty && !fixedRight.equals(right)) {
			carryMap.get(fixedRight).get
		} else { null }


		val carryB = if (!carryMap.get(fixedLeft).isEmpty && !fixedLeft.equals(left)) {
			carryMap.get(fixedLeft).get
		} else { null }   

		(carryA, carryB)
	}

	def getOldSubs(fixedRight: SequentProofNode, fixedLeft: SequentProofNode, mguMap: MMap[SequentProofNode, Substitution]) = {
		val olderA = if (!mguMap.get(fixedRight).isEmpty) {
			mguMap.get(fixedRight).get
		} else { null }

		val olderB = if (!mguMap.get(fixedLeft).isEmpty) {
			mguMap.get(fixedLeft).get
		} else { null }

		(olderA, olderB)
	}

	def getNewFixedNode(fixedNode: SequentProofNode, oldNode: SequentProofNode, oldSub: Substitution, vars: MSet[Var]): SequentProofNode = {
		val out = fixedNode match {
		case Axiom(c) if (oldNode != null && !fixedNode.equals(oldNode)) => {
			new FOSubstitution(fixedNode, oldSub)(vars)
		}
		case _ if (oldNode != null && !fixedNode.equals(oldNode)) => {
			new FOSubstitution(fixedNode, oldSub)(vars)
		}
		case _ => {
			fixedNode
		}
		}
		out
	}

	def getNewFixedNodes(fixedRight: SequentProofNode, fixedLeft: SequentProofNode, right: SequentProofNode, left: SequentProofNode,
			rSub: Substitution, lSub: Substitution, vars: MSet[Var]): (SequentProofNode, SequentProofNode) = {
		val newFixedRight = getNewFixedNode(fixedRight, right, rSub, vars)
				val newFixedLeft = getNewFixedNode(fixedLeft, left, lSub, vars)
				(newFixedRight, newFixedLeft)
	}


	def getCarry(mergedCarry: Sequent) = {
		val testCarry = if (mergedCarry != null) {
			val testAnt = if (mergedCarry.ant != null) {
				mergedCarry.ant
			} else {
				Seq[E]()
			}
			val testSuc = if (mergedCarry.suc != null) {
				mergedCarry.suc
			} else {
				Seq[E]()
			}
			addAntecedents(testAnt.toList) union addSuccedents(testSuc.toList)
		} else {
			null
		}
		testCarry
	}
	
	
	def resolveUsingMultipleCarriedSubs(node: SequentProofNode, fixedRight: SequentProofNode, fixedLeft: SequentProofNode, right: SequentProofNode, left: SequentProofNode, 
			mguMap: MMap[SequentProofNode, Substitution], vars: MSet[Var], carryMap: MMap[SequentProofNode, Sequent], carryMapList: MMap[SequentProofNode, List[Sequent]]) = {
	  							val oMGU = node.asInstanceOf[UnifyingResolution].mgu

									val (carryA, carryB) = getCarries(fixedRight, fixedLeft, right, left, carryMap)

									val (olderA, olderB) = getOldSubs(fixedRight, fixedLeft, mguMap)

									val (newFixedRight, newFixedLeft) = getNewFixedNodes(fixedRight, fixedLeft, right, left, olderA, olderB, vars)

									val (leftMGU, rightMGU) = splitMGU(node, left, right)

									val stuff = generateGoal(fixedLeft, fixedRight, carryA, carryB, olderA, olderB, node.conclusion, oMGU, node, leftMGU, rightMGU)(vars)

									val newGoalD = stuff._1

									var newGoalIfDesperate = null.asInstanceOf[Sequent]

											val out = try {
												UnifyingResolutionMRR(newFixedLeft, newFixedRight, newGoalD)(vars)
											} catch {
											case e: Exception => {

												val triedAll = tryToResolveUsingAllCarrys(node, left, right, fixedLeft, fixedRight, carryMapList, mguMap, vars, false)
														val carriesOut = if (triedAll._1 == null) {
															val triedCon = tryToResolveUsingAllCarrys(node, left, right, fixedLeft, fixedRight, carryMapList, mguMap, vars, true)
																	newGoalIfDesperate = triedCon._2
																	triedCon._1
														} else {
															newGoalIfDesperate = triedAll._2
																	triedAll._1
														}
												tryReversingArguments(newFixedLeft, newFixedRight, newGoalD, vars)

												carriesOut
											}
											}

							var outAfterContraction = out
									val outContracted = Contraction(out)(vars)

									val newSize = (outContracted.conclusion.ant.size + outContracted.conclusion.suc.size)
									val oldSize = (out.conclusion.ant.size + out.conclusion.suc.size)
									var contracted = false
									if (newSize < oldSize) {
										outAfterContraction = outContracted
												contracted = true
									}


							//Note that the axioms used here are never inserted into the final proof
							//They are only used as wrappers as some functions require nodes, not sequents.
							val contractedGoal = if (!contracted) {
								if (newGoalIfDesperate == null) {
									newGoalD
								} else {
									newGoalIfDesperate
								}
							} else {
								if (newGoalIfDesperate == null) {
									Contraction(Axiom(out.conclusion))(vars).conclusion
								} else {
									Contraction(Axiom(newGoalIfDesperate))(vars).conclusion
								}
							}



							val mergedCarry = unionSequents(stuff._3, stuff._4)


									val cleanMGU = if (newGoalIfDesperate == null) {
										findRenaming(newGoalD, out.conclusion)(vars)

									} else {
										findRenaming(newGoalIfDesperate, out.conclusion)(vars)

									}

							val testCarry = getCarry(mergedCarry)

									addCarryToMapList(out, testCarry, carryMapList)

									addToMap(out, testCarry, carryMap)


									mguMap.update(out, stuff._2)
									out
	}

	def findOriginalResolvent(fixedRight: SequentProofNode, fixedLeft: SequentProofNode, right: SequentProofNode, left: SequentProofNode, 
			mguMap: MMap[SequentProofNode, Substitution], vars: MSet[Var], carryMap: MMap[SequentProofNode, Sequent], carryMapList: MMap[SequentProofNode, List[Sequent]]) = {

		val (olderA, olderB) = getOldSubs(fixedRight, fixedLeft, mguMap)

				val (newFixedRight, newFixedLeft) = getNewFixedNodes(fixedRight, fixedLeft, right, left, olderA, olderB, vars)

				var urMRRout = try {
					UnifyingResolutionMRR(newFixedLeft, newFixedRight)(vars)
				} catch {
				case e: MRRException if (e.getMessage != null && e.getMessage.equals("Resolution (MRR): the conclusions of the given premises are not resolvable.")) => {
					UnifyingResolutionMRR(newFixedRight, newFixedLeft)(vars)
				}
				}

		var temp = urMRRout
				while (temp.isInstanceOf[Contraction]) {
					temp = temp.asInstanceOf[Contraction].premise
				}

		urMRRout = temp



				val (carryA, carryB) = getCarries(fixedRight, fixedLeft, right, left, carryMap)

				val resMGU = temp.asInstanceOf[UnifyingResolution].mgu

				val nodeMGU = resMGU
				val newLeftClean = urMRRout.asInstanceOf[UnifyingResolution].leftClean.conclusion
				mguMap.update(urMRRout, resMGU)

				val (leftMGU, rightMGU) = splitMGU(temp, newFixedLeft, newFixedRight)

				val updatedCarryA = updateCarry(carryA, olderA)
				val updatedCarryB = updateCarry(carryB, olderB)


				val finalUpdatedCarryA = updateCarry(updatedCarryA, rightMGU)
				val finalUpdatedCarryB = updateCarry(updatedCarryB, leftMGU)

				val mergedCarry = unionSequents(finalUpdatedCarryB, finalUpdatedCarryA)

				val testCarry = getCarry(mergedCarry)

				val renamingBackward = findRenaming(urMRRout.asInstanceOf[UnifyingResolution].leftClean.conclusion, newFixedLeft.conclusion)(vars)
				val fixedCarry = updateCarry(testCarry, renamingBackward)

				if (testCarry != null) {
					addToMap(urMRRout, testCarry, carryMap)
					addCarryToMapList(urMRRout, testCarry, carryMapList)					
				}
		urMRRout
	}


	def tryToResolveUsingAllCarrys(node: SequentProofNode, left: SequentProofNode, right: SequentProofNode, fixedLeft: SequentProofNode, fixedRight: SequentProofNode, carryMap: MMap[SequentProofNode, List[Sequent]], mguMap: MMap[SequentProofNode, Substitution], vars: MSet[Var], attemptContraction: Boolean): (SequentProofNode, Sequent) = {
		val leftCarryList = if (!carryMap.get(fixedLeft).isEmpty) {
			carryMap.get(fixedLeft).get
		} else {
			List[Sequent]()
		}

		val rightCarryList = if (!carryMap.get(fixedRight).isEmpty) {
			carryMap.get(fixedRight).get
		} else {
			List[Sequent]()
		}

		val finalLeftCarries = (leftCarryList ++ List[Sequent](null.asInstanceOf[Sequent]))
				val finalRightCarries = (rightCarryList ++ List[Sequent](null.asInstanceOf[Sequent]))

				var finalOut = null.asInstanceOf[SequentProofNode]
						var finalGoal = null.asInstanceOf[Sequent]

								for (leftCarry <- finalLeftCarries) {
									for (rightCarry <- finalRightCarries) {
										try {
											val oMGU = node.asInstanceOf[UnifyingResolution].mgu

											//Can't use getCarries here as this is a special case (and in particular, has no map)
													val carryA = if (!fixedRight.equals(right)) {
														rightCarry
													} else { null }

											val carryB = if (!fixedLeft.equals(left)) {
												leftCarry
											} else { null }

											val (olderA, olderB) = getOldSubs(fixedRight, fixedLeft, mguMap)

													val (newFixedRight, newFixedLeft) = getNewFixedNodes(fixedRight, fixedLeft, right, left, olderA, olderB, vars)

													val (leftMGU, rightMGU) = splitMGU(node, left, right)

													val stuff = generateGoal(fixedLeft, fixedRight, carryA, carryB, olderA, olderB, node.conclusion, oMGU, node, leftMGU, rightMGU)(vars)

													val newGoalD = stuff._1

													val contractedNewLeft = if (attemptContraction) {
														val tempConL = Contraction(fixedLeft)(vars)
																if(tempConL.conclusion.logicalSize < fixedLeft.conclusion.logicalSize){
																	tempConL
																} else {
																	fixedLeft
																}
													} else {
														fixedLeft 
													}
											val contractedNewRight =  if (attemptContraction) {
												val tempConR = Contraction(fixedRight)(vars)
														if(tempConR.conclusion.logicalSize < fixedRight.conclusion.logicalSize){
															tempConR
														} else {
															fixedRight
														}
											} else {
												fixedRight 
											}

											val out = UnifyingResolutionMRR(contractedNewLeft, contractedNewRight, newGoalD)(vars)

													val mergedCarry = unionSequents(stuff._3, stuff._4)

													val cleanMGU = findRenaming(newGoalD, out.conclusion)(vars)
													val testCarry = getCarry(mergedCarry)


													mguMap.update(out, stuff._2)

													if (finalOut == null) {
														finalOut = out
																finalGoal = newGoalD
													}

										} catch {
										case e: Exception => {
											println("Attempt failed. Moving on...")
										}
										}
									}
								}
		(finalOut, finalGoal)
	}	



	def makeUnitSequent(u: SequentProofNode, c: E): Sequent = {
		if (isUnitAnt(u)) {
			Sequent()(c)
		} else {
			Sequent(c)()
		}
	}

	def isUnitAnt(u: SequentProofNode): Boolean = {
		if (u.conclusion.ant.size > 0) {
			true
		} else if (u.conclusion.suc.size > 0) {
			false
		} else {
			throw new Exception("Unit check on non-unit node")
		}
	}

	def splitMGU(p: SequentProofNode, l: SequentProofNode, r: SequentProofNode): (Substitution, Substitution) = {
		val ur = p.asInstanceOf[UnifyingResolution]
				val lCleanVars = getSetOfVars(ur.leftClean)
				val rVars = getSetOfVars(r)

				val oldMGU = ur.mgu

				val leftSubOutPairs = MSet[(Var, E)]()
				val rightSubOutPairs = MSet[(Var, E)]()

				for (s <- oldMGU) {
					if (rVars.contains(s._1)) {
						rightSubOutPairs.add(s)
					} else {
						leftSubOutPairs.add(s)
					}
				}

		val lSubOut = Substitution(leftSubOutPairs.toList: _*)
				val rSubOut = Substitution(rightSubOutPairs.toList: _*)

				(lSubOut, rSubOut)
	}

	def generateGoal(fl: SequentProofNode, fr: SequentProofNode, carry: Sequent, carryB: Sequent, older: Substitution,
			olderB: Substitution, oldGoal: Sequent, nodeMGU: Substitution, n: SequentProofNode, lMGU: Substitution, rMGU: Substitution)(implicit uVars: MSet[Var]): (Sequent, Substitution, Sequent, Sequent) = {


		val temp = n 

				val tempMGU = nodeMGU 


				val outSeq = if (carryB != null && carry != null) {

					addAntecedents(
							(temp.conclusion.ant.toList
									++ carry.ant.map(e => older((e))).map(e => rMGU(e))
									++ carryB.ant.map(e => olderB((e))).map(e => lMGU(e)))) union addSuccedents(
											(temp.conclusion.suc.toList
													++ carry.suc.map(e => older((e))).map(e => rMGU(e))
													++ carryB.suc.map(e => olderB((e))).map(e => lMGU(e))))

				} else if (carry == null && carryB != null) {

					addAntecedents((temp.conclusion.ant.toList
							++ carryB.ant.map(e => olderB((e))).map(e => lMGU(e)))) union addSuccedents(temp.conclusion.suc.toList ++ carryB.suc.map(e => olderB((e))).map(e => lMGU(e)))

				} else if (carry != null && carryB == null) {

					addAntecedents((temp.conclusion.ant.toList ++ carry.ant.map(e => older((e))).map(e => rMGU(e)))) union addSuccedents(temp.conclusion.suc.toList ++ carry.suc.map(e => older((e))).map(e => rMGU((e))))

				} else {
					addAntecedents(temp.conclusion.ant.toList) union addSuccedents(temp.conclusion.suc.toList)
				}


		var outB = null.asInstanceOf[Sequent]
				if (carryB != null) {

					val newAnt = carryB.ant.map(e => olderB(e)).map(e => lMGU(e))
							val newSuc = carryB.suc.map(e => olderB(e)).map(e => lMGU(e))

							outB = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
				}


		var outA = null.asInstanceOf[Sequent]
				if (carry != null) {

					val newAnt = carry.ant.map(e => older(e)).map(e => rMGU(e))
							val newSuc = carry.suc.map(e => older(e)).map(e => rMGU(e))

							outA = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
				}

		(outSeq, tempMGU, outA, outB)
	}


	def findUnifiableFormula(f: E, seqHalf: Seq[E])(implicit uVars: MSet[Var]): MSet[E] = {
		val out = MSet[E]()
				for (sf <- seqHalf) {
					if (isUnifiable((f, sf))) {
						out.add(sf)
					}
					if (isUnifiable((sf, f))) {
						out.add(sf)
					}
				}
		out
	}

	def findUnitInSeq(node: SequentProofNode, units: List[SequentProofNode], vars: MSet[Var]): SequentProofNode = {
		if (units.size < 1) {
			return null
		} else {
			val unitToTest = units.head
					if (unitToTest.conclusion.suc.size > 0) {
						val unitFormulas = findUnifiableFormula(unitToTest.conclusion.suc.head, node.conclusion.suc)(vars)
								if (unitFormulas.size > 0) {
									unitToTest
								} else {
									findUnitInSeq(node, units.tail, vars)
								}
					} else {
						val unitFormulas = findUnifiableFormula(unitToTest.conclusion.suc.head, node.conclusion.suc)(vars)
								if (unitFormulas.size > 0) {
									unitToTest
								} else {
									findUnitInSeq(node, units.tail, vars)
								}
					}
		}
	}

	def smartContraction(left: SequentProofNode, right: SequentProofNode, units: List[SequentProofNode], vars: MSet[Var]): SequentProofNode = {
		val newRight = {
				val tempCon = Contraction(right)(vars)
						if (tempCon.conclusion.logicalSize < right.conclusion.logicalSize){
							tempCon
						} else {
							right
						}
		}

		val rightsUnit = findUnitInSeq(newRight, units, vars)

				val rightUnitIsAnt = if (rightsUnit.conclusion.suc.size > 0) {
					false
				} else {
					true
				}

		val newLeftFormulas = if (!rightUnitIsAnt) {
			findUnifiableFormula(rightsUnit.conclusion.suc.head, left.conclusion.ant)(vars)
		} else {
			findUnifiableFormula(rightsUnit.conclusion.ant.head, left.conclusion.suc)(vars)
		}

		val newLeftSequent = if (rightUnitIsAnt) {
			addSuccedents(newLeftFormulas.toList)
		} else {
			addAntecedents(newLeftFormulas.toList)
		}

		val newLeftAx = Axiom(newLeftSequent)
				val newLeftCon = Contraction(newLeftAx)(vars)

				val conSubs = newLeftCon.subs

				val leftSubstituted = applySubs(left, conSubs, vars)

				val leftContractedSmart = Contraction(leftSubstituted)(vars)

				val smarterContractionResolution = try {
					UnifyingResolution(newRight, leftContractedSmart)(vars)
				} catch {
				case e: Exception => {
					if(e.getMessage.equals("Resolution: the resolvent is ambiguous.")){
						UnifyingResolution(leftContractedSmart,newRight)(vars)
					} else {
						throw e 
					}
				}
				}
		smarterContractionResolution
	}

	def applySubs(node: SequentProofNode, subs: List[Substitution], vars: MSet[Var]): SequentProofNode = {
		if (subs.size < 1) {
			node
		} else {
			val newNode = new FOSubstitution(node, subs.head)(vars)
					applySubs(newNode, subs.tail, vars)
		}
	}

	def contractAndUnify(left: SequentProofNode, right: SequentProofNode, vars: MSet[Var], units: List[SequentProofNode]) = {
		if (isUnitClause(left.conclusion)) {
			if (isUnitClause(right.conclusion)) {
				//Both units; no need to contract either
				UnifyingResolution(left, right)(vars)

			} else {
				//only right is non-unit
				val contracted = Contraction(right)(vars)
						if (contracted.conclusion.logicalSize < right.conclusion.logicalSize) {
							finishResolution(left, contracted, true)(vars)
						} else {
							finishResolution(left, right, true)(vars)
						}
			}
		} else {
			if (isUnitClause(right.conclusion)) {
				//only left is non-unit
				val contracted = Contraction(left)(vars)
						if (contracted.conclusion.logicalSize < left.conclusion.logicalSize) {
							finishResolution(contracted, right, false)(vars)
						} else {
							finishResolution(left, right, false)(vars)

						}
			} else {
				//both are non-units
				val contractedL = Contraction(left)(vars)
						val contractedR = Contraction(right)(vars)

						val finalL = if (contractedL.conclusion.logicalSize < left.conclusion.logicalSize) {
							contractedL
						} else {
							left
						}

				val finalR = if (contractedR.conclusion.logicalSize < right.conclusion.logicalSize) {
					contractedR
				} else {
					right
				}        

				try {
					UnifyingResolution(finalL, finalR)(vars)

				} catch {
				case e: Exception => {
					smartContraction(left, right, units, vars)
				}
				}
			}
		}
	}

	def finishResolution(left: SequentProofNode, right: SequentProofNode, leftIsUnit: Boolean)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
		try {
			UnifyingResolution(left, right)(unifiableVariables)
		} catch {
		case e: Exception => {
			if(e.getMessage.equals("Resolution: the resolvent is ambiguous.")){
				multipleResolution(left, right, leftIsUnit)(unifiableVariables)
			} else {
				throw new Exception("Could not invoke multiple resolution")
			}
		}
		}
	}

	def multipleResolution(left: SequentProofNode, right: SequentProofNode, leftIsUnit: Boolean)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
		if (leftIsUnit) {
			//left is unit
			multipleResolutionHelper(left, right, leftIsUnit)
		} else {
			//right is unit
			multipleResolutionHelper(right, left, leftIsUnit)
		}
	}


	def multipleResolutionHelper(unitNodeGiven: SequentProofNode, otherNodeGiven: SequentProofNode, flag: Boolean)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
		//unitNodeGiven is unit
		if (unitNodeGiven.conclusion.suc.size > 0) {
			val unitNodeGivenUnit = unitNodeGiven.conclusion.suc.head

					val listOfThingsToRemove = findUnifiableFormula(unitNodeGivenUnit, otherNodeGiven.conclusion.ant)
					if (listOfThingsToRemove.size < 1) {
						return otherNodeGiven
					}
			val toRemove = listOfThingsToRemove.head

					val newAnt = otherNodeGiven.conclusion.ant.filter(_ != toRemove)
					val newSuc = otherNodeGiven.conclusion.suc
					val goal = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
					val temp = UnifyingResolution(unitNodeGiven, otherNodeGiven, goal)
					if (temp.conclusion.ant.size == 0 && temp.conclusion.suc.size == 0) {
						temp
					} else {
						multipleResolution(unitNodeGiven, temp, flag)
					}
		} else if (unitNodeGiven.conclusion.ant.size > 0) {
			val unitNodeGivenUnit = unitNodeGiven.conclusion.ant.head

					val listOfThingsToRemove = findUnifiableFormula(unitNodeGivenUnit, otherNodeGiven.conclusion.suc)
					if (listOfThingsToRemove.size < 1) {
						return otherNodeGiven
					}
			val toRemove = listOfThingsToRemove.head

					val newAnt = otherNodeGiven.conclusion.ant
					val newSuc = otherNodeGiven.conclusion.suc.filter(_ != toRemove)
					val goal = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
					val temp = UnifyingResolution(unitNodeGiven, otherNodeGiven, goal)
					if (temp.conclusion.ant.size == 0 && temp.conclusion.suc.size == 0) {
						temp
					} else {
						multipleResolution(unitNodeGiven, temp, flag)
					}
		} else {
			throw new Exception("Multiple resolution failed.")
		}
	}

	def apply(proof: Proof[SequentProofNode]): Proof[SequentProofNode] = {
		val collected = collectUnits(proof)

				val units = collected._1
				val varsC = collected._2


				if (units.length == 0) {
					return proof
				}

		try {
			val fixMap = fixProofNodes(units.toSet, proof, varsC)

					def placeLoweredResolution(leftN: SequentProofNode, rightN: SequentProofNode) = {
				try {
					contractAndUnify(leftN, rightN, varsC, units)
				} catch {
				case e: Exception => {
					e.printStackTrace()

					contractAndUnify(rightN, leftN, varsC, units)
				}
				}
			}


			val root = units.map(fixMap).foldLeft(fixMap(proof.root))(placeLoweredResolution)

					val p = Proof(root)
					p
		} catch {
		case e: Exception => {
			throw new CompressionException("FOLowerUnits failed")
		}
		}
	}

}

case class CompressionException(error: String) extends Exception {
	override def getMessage: String = {
	error
}
}