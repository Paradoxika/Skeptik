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
import at.logic.skeptik.proof.sequent.resolution.MRRException
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
import at.logic.skeptik.proof.sequent.resolution.Contraction
import at.logic.skeptik.proof.sequent.resolution.CanRenameVariables
import at.logic.skeptik.proof.sequent.resolution.FindMGU
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents
import java.io.FileWriter

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

//	//(jgorzny) 2 June 2015:
//	//This checks the aux after the original mgu was applied
//	//prevents some terrible attempts to lower
//	//NOTE: p MUST be a unifying resolution node
//	protected def checkForResSmart(safeLiteralsHalf: Set[E], aux: E, p: SequentProofNode, skip: Boolean = false): (Boolean, Substitution) = {
//		if (safeLiteralsHalf.size < 1) {
//			return (false, null)
//		}
//
//		/* 
//		 * unifiableVars might not contain the variables in the aux formulae. When UR(MRR) generates the auxL/auxR formulae,
//		 * it may rename the variables in one premise to a new premise that we just haven't seen yet (and which is resolved out
//		 * in that resolution and thus never really visible in the proof, so we need to check for new variables and
//		 * add them to our list of unifiable variables or the unification might fail.
//		 */
//
//		/*  For example,
//		 * 
//		 *  p(X) |- q(a)     with    q(X) |- 
//		 * 
//		 *  UR might rename the right X as Y, then resolve out to get P(X) |-
//		 *  And while UR used q(Y) |- and recorded the aux formula as such, it didn't rename
//		 *  the right premise, so we never see the variable Y, even though it can be unified.
//		 */
//
//		def oldMGU = p.asInstanceOf[UnifyingResolution].mgu
//				def newAux = if (!skip) { oldMGU(aux) } else { aux }
//		//		    def newAux = oldMGU(aux) //def 4.2 says \sigma_1 should be applied to the axu
//		for (safeLit <- safeLiteralsHalf) {
//			val uvars = getSetOfVars(newAux) //  def 4.2 says the aux formula with the sigma applied should *match* 
//					unify((newAux, safeLit) :: Nil)(uvars) match {
//					case Some(s) => {
//						return (true, s)
//					}
//					case None => {
//						//Do nothing
//					}
//			}
//		}
//		(false, null)
//	}
	
	//(jgorzny) 2 June 2015:
	//This checks the aux after the original mgu was applied
	//prevents some terrible attempts to lower
	//NOTE: p MUST be a unifying resolution node
	protected def checkForResSmart(safeLiteralsHalf: Set[E], aux: E, p: SequentProofNode, skip: Boolean = false): (Boolean, Substitution) = {
		if (safeLiteralsHalf.size < 1) {
			return (false, null)
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
		 var count = 0;
		 var oSub = null.asInstanceOf[Substitution];
		def oldMGU = p.asInstanceOf[UnifyingResolution].mgu
				def newAux = if (!skip) { oldMGU(aux) } else { aux }
		//		    def newAux = oldMGU(aux) //def 4.2 says \sigma_1 should be applied to the axu
		for (safeLit <- safeLiteralsHalf) {
			val uvars = getSetOfVars(newAux) //  def 4.2 says the aux formula with the sigma applied should *match* 
					unify((newAux, safeLit) :: Nil)(uvars) match {
					case Some(s) => {
						count = count + 1
						oSub = s
					  //return (true, s)
					}
					case None => {
						//Do nothing
					}
			}
		}
		val out = count == 1
		(out, oSub)
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
		var out = false
				val sName = getPredName(safe)
				for (lit <- lits) {
					val lName = getPredName(lit)
							val varsX = getSetOfVars(safe) union getSetOfVars(lit)
							val sigmaX = unify((lit, safe) :: Nil)(varsX)      
							if (!sigmaX.isEmpty) {
								val vars = getSetOfVars(safe) //PR
										//        val vars = getSetOfVars(safe) union getSetOfVars(lit)
										val sigma = unify((lit, safe) :: Nil)(vars)
										if (sigma.isEmpty) {
											//          return false

										} else { //PR - this else branch
											out = out || true
										}
							}
				}
		//    true
		out
	}  

	class FOEdgesToDelete extends EdgesToDelete {

		override def nodeIsMarked(node: SequentProofNode): Boolean = {
				// may be optimized (edgesToDelete contains node is checked 3 times)
				node match {
				case _ if ((edges contains node) && edges(node)._2) => true
				case UnifyingResolution(left, right, _, _) if (isMarked(node, left) && isMarked(node, right)) => {
				deleteNode(node)
				true
				}			
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
//				case FOSubstitution(premise,sub) => premise.isInstanceOf[UnifyingResolutionMRR]
				case _                                 => return false
				}
			}
			false
	}
	

	//ensure that the node that will be replacing the unifying resolution is entirely safe  
	protected def finalCheck(safeLit: Sequent, seqToDelete: Sequent, allowSubset: Boolean): (Boolean, Substitution) = {

		if(safeLit.logicalSize < seqToDelete.logicalSize) { return (false, null) }

		def desiredIsContained(safe: Sequent, toDelete: Sequent): (Boolean, Substitution) = {
			if (checkIfConclusionsAreEqual(safe, toDelete)) {
				return (true, Substitution())
			} else if (toDelete.ant.toSet.subsetOf(safe.ant.toSet) && toDelete.suc.toSet.subsetOf(safe.suc.toSet)) {
				return (true, Substitution())
			} else {
				val cVars = getSetOfVars(toDelete.ant: _*) union getSetOfVars(toDelete.suc: _*)

						val (mapIsUniquelyValid, intersectedMap) = computeIntersectedMap(safe, toDelete, cVars, allowSubset)

						if (mapIsUniquelyValid) {
							if (!checkMapSub(intersectedMap, cVars, toDelete, safe)._1) {
								return (false, null)
							} else {
								return (true,checkMapSub(intersectedMap, cVars, toDelete, safe)._2)
							}
						} else {
							val t = checkInvalidMapB(intersectedMap, cVars, toDelete, safe, true)
									return (t == null, t)

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
					(allMatchesOkay, fastFindRenaming(safeClean.conclusion, seqToDelete, false))
				} else {
					(desiredIsContained(safeClean.conclusion, seqToDelete)._1 && allMatchesOkay,desiredIsContained(safeClean.conclusion, seqToDelete)._2)  //PR
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
			safeMap: MMap[SequentProofNode, Sequent], containsFOsubs: Boolean)(p: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
		lazy val fixedLeft = fixedPremises.head;
		lazy val fixedRight = fixedPremises.last;

		var resMap = new MMap[SequentProofNode, MSet[Substitution]]()
				p match {

//		  case FOSubstitution(premise,_) => {
//		    println("FO sub found: " + p)
//		    println("FO- : "  + premise)
//		    println("FO- fl: " + fixedLeft)
//		    println("FO- fr: " + fixedRight)
////		    premise
////		    fixedLeft
////		    p
//		  }
//		  
		  
		  
				case Contraction(source, _) if isMRRContraction(p.asInstanceOf[Contraction]) && !containsFOsubs => {
					try {
//					  if(p.isInstanceOf[FOSubstitution]) { println("OH") }
//					  if(source.isInstanceOf[FOSubstitution]) { println("Con on FO") }
//					  if(fixedLeft.isInstanceOf[FOSubstitution]) { 
//					    println("Con on FO - l")
//					    return fixedLeft.asInstanceOf[FOSubstitution].premise
//					  }
					  if(fixedLeft.isInstanceOf[FOSubstitution]){println("G")}
						val out = Contraction(fixedLeft, p.conclusion)(unifiableVariables)
								p //if we can find the old conclusion from the fixed node, it's the same. memory optimization
					} catch {
					case t: Throwable => {
//					  if(t.isInstanceOf[Exception]) { println(t.getMessage()) }
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
						if(fixedLeft.isInstanceOf[FOSubstitution]){println("H")}
								val newL = Contraction(fixedLeft, lDistinct)(unifiableVariables)
						
//                val newL = if(!fixedLeft.isInstanceOf[FOSubstitution]){
//                  Contraction(fixedLeft, lDistinct)(unifiableVariables)						
//                } else {
//                  fixedLeft
//                }

								val rDistinct = Sequent(fixedRight.conclusion.ant.distinct: _*)(fixedRight.conclusion.suc.distinct: _*)
								if(fixedRight.isInstanceOf[FOSubstitution]){println("I")}
								val newR = Contraction(fixedRight, rDistinct)(unifiableVariables)

//                val newR = if(!fixedRight.isInstanceOf[FOSubstitution]){
//                  Contraction(fixedRight, lDistinct)(unifiableVariables)						
//                } else {
//                  fixedRight
//                }								
								
								if (checkIfConclusionsAreEqual(newR, fixedRight) && checkIfConclusionsAreEqual(newL, fixedLeft)) {
									return p
								}
//								if (checkIfConclusionsAreEqual(right, fixedRight) && checkIfConclusionsAreEqual(left, fixedLeft)) {
//									return p
//								}								

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
					assert(!checkForResSmart(fixedLeft.conclusion.toSetSequent.suc, pivot, p)._1)
					fixedLeft
				}
				case UnifyingResolution(left, right, _, pivot) if (findRenaming(fixedRight.conclusion, p.conclusion)(unifiableVariables) != null) => {
					//If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
					//the fixed parent; so the pivot better be missing.
					assert(!checkForResSmart(fixedRight.conclusion.toSetSequent.ant, pivot, p)._1)
					fixedRight
				}

				// Main case (rebuild a resolution)
				case UnifyingResolution(left, right, auxL, auxR) => {

				  println("Main -  l: " + left)
				  println("Main -  r: " + right)
				  println("Main - fl: " + fixedLeft)
				  println("Main - fr: " + fixedRight)
				  
//				  if(checkIfConclusionsAreEqual(fixedLeft, left)) { return UnifyingResolution(fixedLeft, right)(unifiableVariables) }
				  
					val ambiguousErrorStringMRR = "Resolution (MRR): the resolvent is ambiguous"
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

									val res = UnifyingResolution(fixedLeft, fixedRight)(unifiableVariables)
											res

								}


							} catch {
							case e: Exception => {
							  println("1: " + e.getMessage())
								if (e.getMessage() != null && (e.getMessage.contains(ambiguousErrorString) || e.getMessage.contains(ambiguousErrorStringMRR))) {

									try {
										val fixAmbigAttempt = fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, p.conclusion, false)(unifiableVariables)
										    println("got past FA")
												val greedyAttempt = attemptGreedyContraction(contractIfHelpful(fixedLeft)(unifiableVariables), fixedRight,
														fixedRight, ambiguousErrorString, ambiguousErrorStringMRR, left, right, auxL, auxR, p.conclusion)(unifiableVariables)

														val uv = finalCheck(fixAmbigAttempt.conclusion,greedyAttempt.conclusion,true)._1

														if (checkIfConclusionsAreEqual(fixAmbigAttempt,fixedRight) || checkIfConclusionsAreEqual(fixAmbigAttempt,fixedLeft)
																|| uv
																){

															greedyAttempt
														} else {
															fixAmbigAttempt
														}
									} catch {
									case aasd: Exception => {
									  
									  println("STUB HIT " + aasd.getMessage)
										fixedRight//stub
									}
									}


								} else {

									try {
										val aSwap = UnifyingResolution(fixedRight, fixedLeft)(unifiableVariables)
												aSwap
									} catch {
									case f: Exception => {
										val attemptGreedyFinal = attemptGreedyContraction(contractIfHelpful(fixedLeft)(unifiableVariables), fixedRight,
												fixedRight, ambiguousErrorString, ambiguousErrorStringMRR, left, right, auxL, auxR, p.conclusion)(unifiableVariables)
												attemptGreedyFinal
									}
									}
								}
							}
							}

					val oldSafe = safeMap.get(p).get

							val bothEq = checkIfConclusionsAreEqual(fixedLeft, left) && checkIfConclusionsAreEqual(fixedRight, right)

							val finalOut = if (finalCheck(oldSafe, out.conclusion, true)._1 || bothEq) {
								out
							} else {
								//fixedRight
								if (checkIfConclusionsAreEqual(fixedLeft, left)) {
								  println("01")
//									fixedRight
									if (finalCheck(oldSafe, fixedRight.conclusion, true)._1) {
									println("01a")
									  fixedRight
									} else {
									  println("01b")
										out
//										
//									 if (finalCheck(oldSafe, fixedLeft.conclusion, true)._1) {
//									  println("02a")
//										fixedLeft
//									} else {
//									  println("02b")
//										out
//									}
//										//
									}
								} else if (checkIfConclusionsAreEqual(fixedRight, right)) {
//									fixedLeft
									if (finalCheck(oldSafe, fixedLeft.conclusion, true)._1) {
									  println("02a")
										fixedLeft
									} else {
									  println("02b")
									  out
									  //
//									  									if (finalCheck(oldSafe, fixedRight.conclusion, true)._1) {
//									  println("02a")
//										fixedRight
//									} else {
//									  println("02b")
//										out
//									}
//									  
//									  
//										//
									}
								} else {
									out
								}
							}
					println("MAIN FINALOUT: " + finalOut)
					finalOut
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
				try {
					val fixLeftCon = contractIfHelpful(fixedLeft)(unifiableVariables)
							val fixRightCon = contractIfHelpful(fixedRight)(unifiableVariables) 
							if(fixLeftCon.conclusion.logicalSize < fixedLeft.conclusion.logicalSize ||
									fixRightCon.conclusion.logicalSize < fixedRight.conclusion.logicalSize){
								val quickFinish = UnifyingResolution(fixLeftCon, fixRightCon, oldConclusion)(unifiableVariables)
										return quickFinish
							} else {
								return fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, true)(unifiableVariables)
							}
				} catch {
				case excp: Exception => {
					val ambigFixed = fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, true)(unifiableVariables)
							return ambigFixed
				}
				}
			} catch {
			case h: Exception => {
				//do nothing; we'll do something else below
			}
			}
			try {
				val k = UnifyingResolution(fixedLeft, contractIfHelpful(fixedRight)(unifiableVariables))(unifiableVariables)
						k
			} catch {
			case f: Exception => {
				fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, false)(unifiableVariables)
			}
			}

		}
		case e: Exception => {
 
		  
		  //**2
//			if(checkIfConclusionsAreEqual(fixedLeft, left)) { 
//				return fixedLeft 
//			}
//			if(checkIfConclusionsAreEqual(fixedRight, right)) { 
//				return fixedRight 
//			}

		  println("XX: fr: " + fixedLeft)
		  println("XX: fl: " + fixedRight)
		  println("XX:  l: " + left)
		  println("XX:  r: " + right)
		  			if(checkIfConclusionsAreEqual(fixedLeft, left)) { 
				return fixedRight 
			}
			if(checkIfConclusionsAreEqual(fixedRight, right)) { 
				return fixedLeft 
			}
		  
			//***************************
//			if (checkSubsetOrEquality(true,right.conclusion, fixedRight.conclusion)) {
//				return fixedLeft
//			}
//			if (checkSubsetOrEquality(true, left.conclusion, fixedLeft.conclusion)) {
//				return fixedRight
//			}		  
//			if (checkSubsetOrEquality(true, fixedLeft.conclusion, left.conclusion)) {
//				return fixedRight
//			}		  
//			if (checkSubsetOrEquality(true, fixedRight.conclusion, right.conclusion)) {
//				return fixedLeft
//			}		  		  


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
									if (contractFixedFindsTarget(fixedLeft, oldConclusion) != null && oldConclusion.logicalSize > 0) {
										val t = contractFixedFindsTarget(fixedLeft, oldConclusion)
												t
									} else if (contractFixedFindsTarget(fixedRight, oldConclusion) != null && oldConclusion.logicalSize > 0) {
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
							println("NEVER")
							fixedRight //*1
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
				  if(premise.isInstanceOf[FOSubstitution]){println("A")}
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
		  if(left.isInstanceOf[FOSubstitution]){println("B")}
			val quickFix = UnifyingResolution(Contraction(left), right)
					return quickFix
		} catch {
		case _: Throwable => { //do nothing
		}
		}

		if(right.isInstanceOf[FOSubstitution]){println("C")}
		val quickFixReverse = UnifyingResolution(left, Contraction(right))

				return quickFixReverse

	}

	def fixAmbiguous(fLeft: SequentProofNode, fRight: SequentProofNode, left: SequentProofNode, right: SequentProofNode,
			auxL: E, auxR: E, oldConclusion: Sequent, skip: Boolean, oldNode: SequentProofNode = null)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

     println("Entering FA")
     println("old: " + oldConclusion)
		val samePremises = checkIfConclusionsAreEqual(fLeft, left) && checkIfConclusionsAreEqual(fRight, right)
		if(fLeft.isInstanceOf[FOSubstitution]){println("D")}
		if(fRight.isInstanceOf[FOSubstitution]){println("E")}
				val samePremisesCon = checkIfConclusionsAreEqual(Contraction(fLeft), left) && checkIfConclusionsAreEqual(Contraction(fRight), right)

				if (!skip && (samePremisesCon || (!samePremises && !samePremisesCon))) {
					try {
						val quickFix = tryGreedyContraction(fLeft, fRight)
								return quickFix
					} catch {
					case _: Throwable => { //do nothing - we have work to do.
					}
					}
				}
   println("didn't QF")
		val aVars = getSetOfVars(auxL) union getSetOfVars(auxR)
				val newMGU = unify((auxL, auxR) :: Nil)(aVars).get //should always be non-empty

				val leftEq = findRenaming(fLeft, left) != null
				val rightEq = findRenaming(fLeft, left) != null //TODO: should these be referencing left or right?

				val instantiatedAux = unify((auxL,auxR)::Nil)(getSetOfVars(auxL) union getSetOfVars(auxR))
				
//				if((fLeft.conclusion.ant.contains(auxL) && fLeft.conclusion.suc.contains(auxL)) 
//				  || (fRight.conclusion.ant.contains(auxL) && fRight.conclusion.suc.contains(auxL))){
//				  return oldNode
//				}
//				if((fLeft.conclusion.ant.contains(auxR) && fLeft.conclusion.suc.contains(auxR)) 
//				  || (fRight.conclusion.ant.contains(auxR) && fRight.conclusion.suc.contains(auxR))){
//				  return oldNode
//				}   

				val rightClean = fixSharedNoFilter(right, left,0,unifiableVariables)		    
				val leftClean = fixSharedNoFilter(left, right,0,unifiableVariables)

				val cleaningMGU = findRenaming(left, leftClean)//(getSetOfVars(left))
				val cleaningMGUb = findRenaming(leftClean, left)//(getSetOfVars(left))

				val cleaningMGUX = findRenaming(fLeft, leftClean)//(getSetOfVars(left))
				val cleaningMGUbX = findRenaming(leftClean, fLeft)//(getSetOfVars(left))				

				val fLeftClean = fLeft.conclusion 


				val (auxLtoRemove, auxLsub) = if (!fLeft.conclusion.suc.contains(newMGU(auxL))) {
					val out = findAuxUnifFormula(fLeft.conclusion.suc.toList, newMGU(auxL))
							if (out._1 == null || out._2 == null) { (auxL, Substitution()) } else { out }
				} else {
					(auxL, Substitution())
				}

		val newmguauxlclean = fixSharedNoFilter(Axiom(Sequent(newMGU(auxL))()),Axiom(Sequent(auxLtoRemove)()),0,unifiableVariables)
				val auxrenamingSub = unify((newmguauxlclean.conclusion.ant.head, auxLtoRemove)::Nil)(getSetOfVars(auxLtoRemove)) match {
				case Some(u) => {u}
				case _ => null
		}

		val removeMGUl = if (!fLeft.conclusion.suc.contains(auxL)){
			newMGU
		} else {
			Substitution()
		}
		
		println("auxLtoRemove: " + auxLtoRemove)

		val (leftRemainder, leftSub) = findRemainder(fLeftClean, auxLtoRemove, Substitution(), leftEq, false)

				val fRightClean = fRight.conclusion

				val (auxRtoRemove, auxRsub) = if (!fRight.conclusion.ant.contains(auxR)) {
					val out = findAuxUnifFormula(fRight.conclusion.ant.toList, auxR)
							if(out._1 == null || out._2 == null) { (auxR,Substitution())  } else { out }
				} else {
					(auxR,Substitution())
				}				

		if(!auxR.equals(auxRtoRemove)){ 				  
			val outCount = countAuxUnifFormula(fRight.conclusion.ant.toList, auxR)
					if(outCount > 1) {return UnifyingResolution(left,right,oldNode.conclusion)(unifiableVariables)}
		}
		if(!auxL.equals(auxLtoRemove)){ 				  
			val outCount = countAuxUnifFormula(fLeft.conclusion.suc.toList, auxL)
					if(outCount > 1) {return UnifyingResolution(left,right,oldNode.conclusion)(unifiableVariables)}
		}				

		println("auxR: " + auxR)
		println("auxL: " + auxL)
		val removeMGU = if (!fRight.conclusion.ant.contains(auxR)){
			newMGU
		} else {
			Substitution()
		}

		println("auxRtoRemove: " + auxRtoRemove)
		
		val (rightRemainder, rightSub) = findRemainder(fRightClean, auxRtoRemove, Substitution(), rightEq, true) //TODO: should this "Substitution()" be "newMGU"?

				val rightRemainderWithNewMGU = makeFOSub(Axiom(rightRemainder), newMGU).conclusion

				val tempLeft = makeFOSub(makeFOSub(Axiom(leftRemainder), leftSub), newMGU)

				val tempRight = Axiom(rightRemainderWithNewMGU)
				val cleanLeftRemainder = fixSharedNoFilter(tempLeft, tempRight, 0, unifiableVariables).conclusion

				println("RR: " + rightRemainderWithNewMGU)
	      println("removeMGU:  " + removeMGU)
	      println("rightSub: " + rightSub)
	      println("newmgu: " + newMGU)
	      
	      println("leftSub: " + leftSub)
	      println("removeMGUl: " + removeMGUl)
	      
	      val rightRemovalSub = unify((auxRtoRemove,auxR)::Nil)(getSetOfVars(auxRtoRemove)) match {
		  case Some(s) => { s} 
		  case None => Substitution()
		}
		    println("rightRemovalSub: " + rightRemovalSub)
	      
				val newTarget = (applySub(rightRemainderWithNewMGU,rightRemovalSub)).union(applySub(tempLeft.conclusion, auxLsub))   
//				val newTarget = rightRemainderWithNewMGU.union(applySub(tempLeft.conclusion, auxLsub))   //

				
				val newFinalRight = findTargetIfEqual(rightEq, right, fLeft)
				val newFinalLeft = findTargetIfEqual(leftEq, left, fRight)

				try{
					val toReturn = UnifyingResolution(fLeft, fRight, newTarget)
							return toReturn
				} catch {
				case y: Exception => {
				}
				}

		val out =
				try {
					try {

						try { 
							val o = UnifyingResolutionMRR(newFinalLeft, newFinalRight, oldConclusion)
									o
						} catch {
						case er: Exception => {
							val o = UnifyingResolutionMRR(newFinalRight, newFinalLeft, oldConclusion)

									o
						}
						}
					} catch {
					case e: Exception => {
						if (e.getMessage.contains("Cannot find desired resolvent")) {
							UnifyingResolution(contractIfHelpful(newFinalLeft), contractIfHelpful(newFinalRight), contractIfHelpful(Axiom(oldConclusion)).conclusion)
						} else {
							try{
								UnifyingResolution(fRight, fLeft)
							} catch {
							case g: Exception => {
								UnifyingResolution(fLeft,fRight)

							}
							}

						}
					}
					}
				} catch {
				case f: Exception => {
//					UnifyingResolutionMRR(fLeft, fRight, newTarget)
				  println("fleft> " + contractIfHelpful(fLeft))
				  println("fright>" +  contractIfHelpful(fRight))
				  println("Last attempt: " + contractIfHelpful(Axiom(newTarget), true).conclusion)
					UnifyingResolutionMRR(contractIfHelpful(fLeft), contractIfHelpful(fRight), contractIfHelpful(Axiom(newTarget), true).conclusion)
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
	  if(fixed.isInstanceOf[FOSubstitution]){println("F")}
		return Contraction(fixed, original.conclusion)

	}

	def findAuxUnifFormula(half: List[E], target: E): (E, Substitution) = {
		for(h <- half){
			val hSub = unifiesRenamingOnly(h,target) 
					if (hSub != null){ return (h,hSub) }//TODO: rename
		}
		(null,null)
	}

	def countAuxUnifFormula(half: List[E], target: E): Int = {
		var count = 0;
		for(h <- half){
			val hSub = unifiesRenamingOnly(h,target) 
					if (hSub != null){ count = count + 1 }//TODO: rename
		}
		count
	}

	def unifiesRenamingOnly(s: E, t: E): Substitution = {
		val u = getUnifier(s,t)(getSetOfVars(s))
				if (u == null) { 
					return null }
		u
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
	  var containsFOsubs = false;
	  
		val edgesToDelete = new FOEdgesToDelete()
		val safeMap = new MMap[SequentProofNode, Sequent]()
		def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
			val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
					safeMap.put(p, safeLiterals.toSeqSequent)
					p match {

					case UnifyingResolution(left, right, auxL, auxR) => {
						val auxLcheck = checkForResSmart(safeLiterals.suc, auxL, p)

								val sigmaL = auxLcheck._2 

								val auxRcheck = checkForResSmart(safeLiterals.ant, auxR, p)
								val sigmaR = auxRcheck._2 

								val auxLfinalCheck = if (auxLcheck._1) { finalCheck(safeLiterals.toSeqSequent, applySub(left.conclusion, sigmaL), true) } else { (false, null) }


						if (auxLcheck._1 && auxLfinalCheck._1 && auxLfinalCheck._2 != null && sigmaL != null && !auxRcheck._1) {
							  if(left.isInstanceOf[FOSubstitution]) { println("marking an FO sub") }
							  if(right.isInstanceOf[FOSubstitution]) { println("marking an FO sub") }
							  if(p.isInstanceOf[FOSubstitution]) { println("marking an FO sub") }
							  println("old mgu: " + p.asInstanceOf[UnifyingResolution].mgu)
						  println("auxL " + sigmaL(auxL) + " should be in the suc of " + safeLiterals)
						  println("sigmaL: " + sigmaL)
							  edgesToDelete.markRightEdge(p)
						} else {

							val auxRfinalCheck = if (auxRcheck._1) { finalCheck(safeLiterals.toSeqSequent, applySub(right.conclusion, sigmaR), true) } else { (false, null) }
							if(auxRcheck._1 && auxRfinalCheck._1 && auxRfinalCheck._2 != null && sigmaR != null && !auxLcheck._1){
							  if(left.isInstanceOf[FOSubstitution]) { println("marking an FO sub") }
							  if(right.isInstanceOf[FOSubstitution]) { println("marking an FO sub") }
							  if(p.isInstanceOf[FOSubstitution]) { println("marking an FO sub") }
							  println("old mgu: " + p.asInstanceOf[UnifyingResolution].mgu)
							  println("auxR " + sigmaR(auxR) + " should be in the ant of " + safeLiterals)
							  println("sigmaR: " + sigmaR)
								edgesToDelete.markLeftEdge(p)
							}
						}
					}

					case FOSubstitution(_,_) => { containsFOsubs = true }
					
					case _ => 
			}
			(p, safeLiterals)
		}
		nodeCollection.bottomUp(visit)
		(edgesToDelete, safeMap, containsFOsubs)
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
