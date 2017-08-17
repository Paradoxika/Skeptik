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

		def oldMGU = p.asInstanceOf[UnifyingResolution].mgu
				//    def newAux = if (!skip) { oldMGU(aux) } else { aux }
//				def newAux = aux //PR
		    def newAux = oldMGU(aux) //def 4.2 says \sigma_1 should be applied to the axu
				for (safeLit <- safeLiteralsHalf) {
					//      println("newAux: " + newAux + " safeLit: " + safeLit)
					//val uvars = (getSetOfVars(newAux) union getSetOfVars(safeLit))
				  val uvars = getSetOfVars(newAux) //  def 4.2 says the aux formula with the sigma applied should *match* 
							unify((newAux, safeLit) :: Nil)(uvars) match {
							case Some(s) => {
								return (true, s)
							}
							case None => {
								//Do nothing
							}
					}
				}
		//    println("checkForResSmart - false")
		(false, null)
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

	//TODO: when this is used, the safe is actually the list 'lits'
	//  def checkAll(lits: Set[E], safe: E): Boolean = {
	//    val sName = getPredName(safe)
	//    for (lit <- lits) {
	//      val lName = getPredName(lit)
	//      if (lName.equals(sName)) {
	//        val vars = getSetOfVars(safe) //PR
	////        val vars = getSetOfVars(safe) union getSetOfVars(lit)
	//        val sigma = unify((lit, safe) :: Nil)(vars)
	//        if (sigma.isEmpty) {
	//          println("CheckAll returning false because of " + lit + " and " + safe)
	//          return false
	//        
	//        } else { //PR - this else branch
	//          println("CheckAll cleared " +  lit + " and " + safe)
	//        }
	//      }
	//    }
	//    true
	//  }

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
											//          println("CheckAll returning false because of " + lit + " and " + safe)
											//          return false

										} else { //PR - this else branch
											//          println("CheckAll cleared " +  lit + " and " + safe)
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
	protected def finalCheck(safeLit: Sequent, seqToDelete: Sequent, allowSubset: Boolean): (Boolean, Substitution) = {

	  if(safeLit.logicalSize < seqToDelete.logicalSize) { return (false, null) }
	  
		def desiredIsContained(safe: Sequent, toDelete: Sequent): (Boolean, Substitution) = {
			if (checkIfConclusionsAreEqual(safe, toDelete)) {
				return (true, Substitution())
			} else if (toDelete.ant.toSet.subsetOf(safe.ant.toSet) && toDelete.suc.toSet.subsetOf(safe.suc.toSet)) {
				return (true, Substitution())
			} else {
//			  println("checking the hard way.")
//			  println("safe:     " + safe)
//			  println("toDelete: " + toDelete)
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

//		println("checking
		
		def antVars = getSetOfVars(seqToDelete.ant: _*)
				def sucVars = getSetOfVars(seqToDelete.suc: _*)
				def antVarsB = getSetOfVars(safeLit.ant: _*)
				def sucVarsB = getSetOfVars(safeLit.suc: _*)
				def allvars = MSet[Var]() ++ antVars ++ sucVars ++ antVarsB ++ sucVarsB
				def safeClean = fixSharedNoFilter(Axiom(safeLit), Axiom(seqToDelete), 0, allvars)
				def vars = MSet[Var]() ++ antVars ++ sucVars

				val allMatchesOkay = checkAllPairs(seqToDelete, safeClean.conclusion)
				//    println("AMO: " + allMatchesOkay)
				if (fastFindRenaming(safeClean.conclusion, seqToDelete, false) != null) {
//				    println("ffr: " + safeClean + " " + seqToDelete)
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
//						  println("123: k: " + k)
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
//								  println("RESp: fl: " + fixedLeft)
//								  println("RESp: fr: " + fixedRight)
//								  println("RESp: l: " + left)
//								  println("RESp: r: " + right)
//								  println("RESp:oc: " + p.conclusion)
//									val res = UnifyingResolutionMRR(fixedLeft, fixedRight)(unifiableVariables)
									val res = UnifyingResolution(fixedLeft, fixedRight)(unifiableVariables)
//									println("RESp: " + res)
											res
								}

							} catch {
							case e: Exception => {
								if (e.getMessage() != null && e.getMessage.contains(ambiguousErrorString)) {
									fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, p.conclusion, false)(unifiableVariables)
								} else {
								  println("111: " + e.getMessage())
									try {
										val a = UnifyingResolution(fixedRight, fixedLeft)(unifiableVariables)
												a
									} catch {
									case f: Exception => {
									  println("222: " + f.getMessage())
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

							if (finalCheck(oldSafe, out.conclusion, true)._1 || bothEq) {
								out
							} else {
								//fixedRight
								if (checkIfConclusionsAreEqual(fixedLeft, left)) {
									fixedRight
									if (finalCheck(oldSafe, fixedRight.conclusion, true)._1) {
										fixedRight
									} else {
										out
									}
								} else if (checkIfConclusionsAreEqual(fixedRight, right)) {
									fixedLeft
									if (finalCheck(oldSafe, fixedLeft.conclusion, true)._1) {
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

	  println("Attempting greedy")
	  println("fixedLeft:   " + fixedLeft)
	  println("fixedRight:  " + fixedRight)
	  println("nfixedRight: " + newFixedRight)
	  println("left:        " + left)
	  println("right:       " + right)
		try {
			UnifyingResolution(fixedLeft, newFixedRight)(unifiableVariables)
		} catch {
		case e: Exception if (e.getMessage() != null && (e.getMessage.contains(ambiguousErrorString) || e.getMessage.contains(ambiguousErrorStringMRR))) => {
//		  println("444: " + e.getMessage())
			try {
				if (checkIfConclusionsAreEqual(contractIfHelpful(fixedLeft)(unifiableVariables), left) && checkIfConclusionsAreEqual(contractIfHelpful(fixedRight)(unifiableVariables), right)) {
					//If the fixed are the same as the old, nothing is changed in this part. Use the old conclusion as a goal
					//to fix the ambiguity; greedy contraction risks the proof failing to end with the empty sequent.
//				  println("444a")
					val success = UnifyingResolution(contractIfHelpful(fixedLeft)(unifiableVariables), contractIfHelpful(fixedRight)(unifiableVariables), oldConclusion)(unifiableVariables)
							return success
				}
				if (checkIfConclusionsAreEqual(fixedLeft, left) && checkIfConclusionsAreEqual(fixedRight, right)) {
					//If the fixed are the same as the old, nothing is changed in this part. Use the old conclusion as a goal
					//to fix the ambiguity; greedy contraction risks the proof failing to end with the empty sequent.
//				  println("444b")
					val success = UnifyingResolution(fixedLeft, fixedRight, oldConclusion)(unifiableVariables)
							return success
				}
				try {
//				   if (oldConclusion.logicalSize > 0){
				  val fixLeftCon = contractIfHelpful(fixedLeft)(unifiableVariables)
				  val fixRightCon = contractIfHelpful(fixedRight)(unifiableVariables) 
           if(fixLeftCon.conclusion.logicalSize < fixedLeft.conclusion.logicalSize ||
                 fixRightCon.conclusion.logicalSize < fixedRight.conclusion.logicalSize){
				  val quickFinish = UnifyingResolution(fixLeftCon, fixRightCon, oldConclusion)(unifiableVariables)
//				   println("aaa " + contractIfHelpful(fixedLeft)(unifiableVariables))
//				   println("aaa returning: " + quickFinish)
//				   println("aaa old: " + oldConclusion)
				   return quickFinish
				   } else {
				     return fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, true)(unifiableVariables)
				   }
				} catch {
				  case excp: Exception => {
				    return fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, true)(unifiableVariables)
				  }
				}
//				return fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, true)(unifiableVariables)
			} catch {
			case h: Exception => {
//			  println("555 " + h.getMessage())
				//do nothing; we'll do something else below
			}
			}
			try {
				val k = UnifyingResolution(fixedLeft, contractIfHelpful(fixedRight)(unifiableVariables))(unifiableVariables)
//				println("XXX " + k)
						k
			} catch {
			case f: Exception => {
//			  println("666" + f.getMessage())
				fixAmbiguous(fixedLeft, fixedRight, left, right, auxL, auxR, oldConclusion, false)(unifiableVariables)
			}
			}

		}
		case e: Exception => {
//		  println("777 " + e.getMessage())
//		  println("oldConclusion: " + oldConclusion)
		  
		  if(checkIfConclusionsAreEqual(fixedLeft, left)) { 
//		    println("zzz1"); 
		  return fixedLeft }
		  if(checkIfConclusionsAreEqual(fixedRight, right)) { 
//		    println("zzz2");
		  return fixedRight }
		  
		  if (checkSubsetOrEquality(true,right.conclusion, fixedRight.conclusion)) {
//					  println("011e")
						return fixedLeft
		  }
		  if (checkSubsetOrEquality(true, left.conclusion, fixedLeft.conclusion)) {
//					  println("011f")
						return fixedRight
		  }		  
		  if (checkSubsetOrEquality(true, fixedLeft.conclusion, left.conclusion)) {
//					  println("011g")
						return fixedRight
		  }		  
		  if (checkSubsetOrEquality(true, fixedRight.conclusion, right.conclusion)) {
//					  println("011h")
						return fixedLeft
		  }		  		  
		  		  
		  
			val oldConclusionIsNotEmpty = !(oldConclusion.ant.size == 0 && oldConclusion.suc.size == 0)
					if (checkIfConclusionsAreEqual(fixedRight, fixedLeft)) {
//					  println("00")
						fixedRight
					} else if (checkSubsetOrEquality(true, fixedRight.conclusion, oldConclusion)) {
//					  println("01")
						fixedRight
//					} else if (checkSubsetOrEquality(true, oldConclusion, fixedRight.conclusion)) {
//					  println("01a")
//					  fixedRight						
					} else if (checkSubsetOrEquality(true, fixedLeft.conclusion, oldConclusion)) {
//					  println("02")
						fixedLeft
					} else {

						try {

							val out =
									if (contractFixedFindsTarget(fixedLeft, oldConclusion) != null && oldConclusion.logicalSize > 0) {
//										println("05")
									  val t = contractFixedFindsTarget(fixedLeft, oldConclusion)
//									  println("t: " + t)
												t
									} else if (contractFixedFindsTarget(fixedRight, oldConclusion) != null && oldConclusion.logicalSize > 0) {
//									  println("06")
										val t = contractFixedFindsTarget(fixedRight, oldConclusion)
												t
									} else {

										try {
//										  println("07")
											UnifyingResolutionMRR(newFixedRight, fixedLeft)(unifiableVariables)
										} catch {
										case g: Exception => {
											g.printStackTrace()
//											println("08")
											UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables)
										}
										}
									}
//							println("out: " + out)
							out
						} catch {
						case f: Exception => {
//						  println("09xxx")
//						  println("l:  " + left)
//						  println("fl: " + fixedLeft)
//						  println("r:  " + right)
//						  println("fr: " + fixedRight)
							f.printStackTrace()
							fixedLeft
//							fixedRight

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
//		  println("TGC: " + Contraction(left).subs)
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
			auxL: E, auxR: E, oldConclusion: Sequent, skip: Boolean, oldNode: SequentProofNode = null)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

	  println("entering FA")
	  		    println("actual fleft? " + fLeft)
		    println("actual fright? " + fRight)

	  				println("left: " + left)
				println("right:" + right)	
				        println("oc: " + oldConclusion)

    val samePremises = checkIfConclusionsAreEqual(fLeft, left) && checkIfConclusionsAreEqual(fRight, right)
    val samePremisesCon = checkIfConclusionsAreEqual(Contraction(fLeft), left) && checkIfConclusionsAreEqual(Contraction(fRight), right)
    
//    val samePremises = false
				        
    println("samePremises: " + samePremises)
    
		if (!skip && (samePremisesCon || (!samePremises && !samePremisesCon))) {
			try {
				val quickFix = tryGreedyContraction(fLeft, fRight)
				    println("returning QF " + quickFix)
						return quickFix
			} catch {
			case _: Throwable => { //do nothing - we have work to do.
			}
			}
		}

		val aVars = getSetOfVars(auxL) union getSetOfVars(auxR)
				val newMGU = unify((auxL, auxR) :: Nil)(aVars).get //should always be non-empty

				val leftEq = findRenaming(fLeft, left) != null
				val rightEq = findRenaming(fLeft, left) != null //TODO: should these be referencing left or right?
				
				val instantiatedAux = unify((auxL,auxR)::Nil)(getSetOfVars(auxL) union getSetOfVars(auxR))
				
//				println("vars??? " + unifiableVariables)
//		    println("actual fleft? " + fLeft)
//		    
		    val rightClean = fixSharedNoFilter(right, left,0,unifiableVariables)
//		    println("rightclean--: " + rightClean)
		    
		    val leftClean = fixSharedNoFilter(left, right,0,unifiableVariables)
//		    println("leftClean--: " + leftClean)		    
		    
				val cleaningMGU = findRenaming(left, leftClean)//(getSetOfVars(left))
				val cleaningMGUb = findRenaming(leftClean, left)//(getSetOfVars(left))

//				println("cleaningMGU:  " + cleaningMGU)
//				println("cleaningMGUb: " + cleaningMGUb)
				
				val cleaningMGUX = findRenaming(fLeft, leftClean)//(getSetOfVars(left))
				val cleaningMGUbX = findRenaming(leftClean, fLeft)//(getSetOfVars(left))				
//				println("cleaningMGUX:  " + cleaningMGU)
//				println("cleaningMGUbX: " + cleaningMGUb)
				
				val fLeftClean = fLeft.conclusion 

//				println("auxL: " + auxL)
//				println("auxR: " + auxR)
//				println("mgu: " + newMGU)
//				
//				println("instantiated auxL: " + newMGU(auxL))
//				println("to remove: " + newMGU(cleaningMGUb(auxL)) )
//				println("to remove b: " + cleaningMGU(auxR))
				
//				println("newmgu(auxl): " + newMGU(auxL))
				
				
				val (auxLtoRemove: E, auxLsub) = if (!fLeft.conclusion.suc.contains(newMGU(auxL))) {
//				  println("aa")
				  findAuxUnifFormula(fLeft.conclusion.suc.toList, newMGU(auxL))
				} else {
				  (auxL, Substitution())
				}
				
//		println("auxLtoRemove " + auxLtoRemove)
//		println("auxLsub " + auxLsub)
		
						val newmguauxlclean = fixSharedNoFilter(Axiom(Sequent(newMGU(auxL))()),Axiom(Sequent(auxLtoRemove)()),0,unifiableVariables)
						val auxrenamingSub = unify((newmguauxlclean.conclusion.ant.head, auxLtoRemove)::Nil)(getSetOfVars(auxLtoRemove)) match {
		  case Some(u) => {u}
		  case _ => null
						}
//						println("wtf-: " + auxrenamingSub)
//						println("wtf: " + newmguauxlclean)
//						
				 val removeMGUl = if (!fLeft.conclusion.suc.contains(auxL)){
		      newMGU
		    } else {
		      Substitution()
		    }
		
//				val (leftRemainder, leftSub) = findRemainder(fLeftClean, auxL, newMGU, leftEq, false)
				val (leftRemainder, leftSub) = findRemainder(fLeftClean, auxLtoRemove, Substitution(), leftEq, false)
		
//				println("leftRemainder: " + leftRemainder)
//				println("leftSub: " + leftSub)
				
//				val leftRemainderUpdated = applySub(leftRemainder,auxrenamingSub)
//				println("leftRemainderUpdated: " + leftRemainderUpdated)
				
				val fRightClean = fRight.conclusion

				val auxRtoRemove = if (!fRight.conclusion.ant.contains(auxR)) {
//				  println("bb")
				  findAuxUnifFormula(fRight.conclusion.ant.toList, auxR)
				} else {
				  auxR
				}				
		
		    val removeMGU = if (!fRight.conclusion.ant.contains(auxR)){
		      newMGU
		    } else {
		      Substitution()
		    }
//		    println("auxRtoRemove: " + auxRtoRemove) 
				
				val (rightRemainder, rightSub) = findRemainder(fRightClean, auxR, Substitution(), rightEq, true) //TODO: should this "Substitution()" be "newMGU"?
//val (rightRemainder, rightSub) = findRemainder(fRightClean, auxR, newMGU, rightEq, true) 		 //needed for 1662
//		val (rightRemainder, rightSub) = findRemainder(fRightClean, auxRtoRemove, removeMGU, rightEq, true) 		
				val rightRemainderWithNewMGU = makeFOSub(Axiom(rightRemainder), newMGU).conclusion
				
//				println("right remainder final? " + rightRemainderWithNewMGU)
				
				val tempLeft = makeFOSub(makeFOSub(Axiom(leftRemainder), leftSub), newMGU)
//				val tempLeft = Axiom(leftRemainderUpdated)
//				println("templeft: " + tempLeft)
				
				val tempRight = Axiom(rightRemainderWithNewMGU)
				val cleanLeftRemainder = fixSharedNoFilter(tempLeft, tempRight, 0, unifiableVariables).conclusion
				
				
//				println("cleanLeftRemainder: " + cleanLeftRemainder)
//		    println("templeft: (before auxL????) " + tempLeft.conclusion)
//				println("tempLeft: " + applySub(tempLeft.conclusion, auxLsub)) //auxLsub
//				val newTarget = rightRemainderWithNewMGU.union(tempLeft.conclusion)   
				val newTarget = rightRemainderWithNewMGU.union(applySub(tempLeft.conclusion, auxLsub))   

				val newFinalRight = findTargetIfEqual(rightEq, right, fLeft)
				val newFinalLeft = findTargetIfEqual(leftEq, left, fRight)
				
				println("FA: nfr: " + newFinalRight)
        println("FA: nfr: " + newFinalLeft)
        println("FINAL TARGET: " + newTarget)
        
        try{
          val toReturn = UnifyingResolution(fLeft, fRight, newTarget)
          println("toReturn: " + toReturn)
          return toReturn
        } catch {
          case y: Exception => {
            println("yyyyyyy:" + y.getMessage()) 
            }
        }
        
				val out =
				try {
					try {
//						val o = UnifyingResolutionMRR(newFinalLeft, newFinalRight, oldConclusion)
						println("FA: o??? " + o)
//								o
					  try { 
					     val o = UnifyingResolutionMRR(newFinalLeft, newFinalRight, oldConclusion)
						println("FA: o???a " + o)
								o
					  } catch {
					    case er: Exception => {
					      val o = UnifyingResolutionMRR(newFinalRight, newFinalLeft, oldConclusion)
						println("FA: o???b " + o)
						println("FA: o???b nfr: " + newFinalRight)
						println("FA: o???b nfl: " + newFinalLeft)
								o
					    }
					  }
					} catch {
					case e: Exception => {
//					  println("needs swap?")
						if (e.getMessage.contains("Cannot find desired resolvent")) {
							UnifyingResolution(contractIfHelpful(newFinalLeft), contractIfHelpful(newFinalRight), contractIfHelpful(Axiom(oldConclusion)).conclusion)
						} else {
//						  				    	UnifyingResolution(fRight, fLeft)

						  try{
				    	UnifyingResolution(fRight, fLeft)
						  } catch {
						    case g: Exception => {
				    	UnifyingResolution(fLeft,fRight)
						      
						    }
						  }
//						  //
//						  try {
//						    println("A")
//							UnifyingResolution(fRight, fLeft)
//						  } catch {
//						    case g: Exception => {
//						      UnifyingResolution(fLeft, fRight)
//						    }
//						  }
//						  //
							
						}
					}
					}
				} catch {
				case f: Exception => {
				  println("B " + f.getMessage())
				  println("target: " + newTarget)
					UnifyingResolutionMRR(fLeft, fRight, newTarget)
				  println("cfl: " + contractIfHelpful(fLeft))
				      println("cfr: " + contractIfHelpful(fRight))
				      println("ct:  " + contractIfHelpful(Axiom(newTarget)).conclusion)
				  UnifyingResolutionMRR(contractIfHelpful(fLeft), contractIfHelpful(fRight), contractIfHelpful(Axiom(newTarget)).conclusion)
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

	def findAuxUnifFormula(half: List[E], target: E): (E, Substitution) = {
	  for(h <- half){
	    val hSub = unifiesRenamingOnly(h,target) 
	    if (hSub != null){ return (h,hSub) }//TODO: rename
	  }
	  (null,null)
	}
	
	
	def unifiesRenamingOnly(s: E, t: E): Substitution = {
	  val u = getUnifier(s,t)(getSetOfVars(s))
	  if (u == null) { return null }
	  u
	}
	
	def findRemainder(seq: Sequent, target: E, mgu: Substitution, applySub: Boolean, removeFromAnt: Boolean)(implicit unifiableVariables: MSet[Var]): (Sequent, Substitution) = {
		def remove(e: E, list: List[E]) = list diff List(e)
		
//		println("trying to remove: " + mgu(target))
		
		val (newAnt, antSub) = if (removeFromAnt) { (remove(mgu(target), seq.ant.toList), Substitution()) } else { (seq.ant.toList, null) }
		val (newSuc, sucSub) = if (!removeFromAnt) { (remove(mgu(target), seq.suc.toList), Substitution()) } else { (seq.suc.toList, null) }

		val subOut = if (antSub != null) { antSub } else { sucSub } //at least one of these must be non-empty
		//both should never be empty
    
		val out = addAntecedents(newAnt) union addSuccedents(newSuc)
//		println("Remainder will be: " + out + " from " + seq)
		(out, subOut)
	}

}

abstract class FOAbstractRPIAlgorithm
extends FOAbstractRPILUAlgorithm with CanRenameVariables {

	//  def findActualAux(seqHalf: Seq[E], aux: E, mgu: Substitution): E = {
	//    for (s <- seqHalf) {
	//      if (mgu(s).equals(aux)) {
	//        return s
	//      }
	//    }
	//    aux
	//  }

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
					//          println("ADDING auxRb: " + auxRb)
					addLiteralSmart(safeLiterals, auxRb, false)
		}

		case (child @ UnifyingResolution(left, right, auxL, auxR), safeLiterals) if right == parent =>
		if (edgesToDelete.isMarked(child, left)) {
			safeLiterals
		} else {
			val sub = child.asInstanceOf[UnifyingResolution].mgu
					def auxLb = sub(auxL)
					//          println("ADDING auxLb: " + auxLb)
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

  //TODO: debugging? can remove?
	def wouldChangeMatter(a: Substitution, b: Substitution, sl: Sequent, auxR: E, auxL: E, right: SequentProofNode, left: SequentProofNode, 
	    marked: String, newLeft: Sequent, ns: Substitution) = {



		val fw = new FileWriter("checking-subs.txt", true)
		try {
//			println("FIRST SUB:  " + a)
//			println("SECOND SUB: " + b)  
			fw.write("FIRST SUB:  " + a + "\n")
			fw.write("SECOND SUB: " + b + "\n")
			val contained = if(a != null && b != null) { a.toList.forall(b.toList.contains) } else { false }
			fw.write("F in S?     " + contained + "\n")
//			print("F in S?     " + contained + "\n")

			if(!contained){
				fw.write("AUXR: " + auxR + "\n")
				fw.write("AUXL: " + auxL + "\n")
				fw.write("SAFE: " + sl + "\n")
				fw.write("RIGHT: " + right + "\n")
				fw.write("LEFT: " + left + "\n")
				fw.write(marked + "\n")


//				print("AUXR: " + auxR + "\n")
//				print("AUXL: " + auxL + "\n")
//				print("SAFE: " + sl + "\n")
//				print("RIGHT: " + right + "\n")
//				print("LEFT: " + left + "\n")
//				print(marked + "\n")    
				
				
				fw.write("NEWLEFT:      " + newLeft  + "\n")
//				println("ns: " + ns)
				
				val newLeftWithAuxSub = Sequent(newLeft.ant.map{ x: E => a(x) }.toSeq: _*)(newLeft.suc.map{ x: E => a(x) }.toSeq: _*)
				fw.write("NEWLEFTsub'd: " + newLeftWithAuxSub + "\n")
//				println("NEWLEFTsub'd: " + newLeftWithAuxSub)
				val newCheckResult = finalCheck(sl, newLeftWithAuxSub, false)//should this be false?
				fw.write("Previous second check was true (in order to get here). New check result is: " + newCheckResult + "\n")
//				print("Previous second check was true (in order to get here). New check result is: " + newCheckResult + "\n")
				
			}
		}
		finally fw.close() 
	}  


	//Purely a debugging method. Can be removed. Should not be included for experiments.
	def isSubSubstitutionAndPrint(a: Substitution, b: Substitution, sl: Sequent, auxR: E, auxL: E, right: SequentProofNode, left: SequentProofNode, marked: String) = {
//		println("FIRST SUB:  " + a)
//		println("SECOND SUB: " + b)



		val fw = new FileWriter("checking-subs-" + "aug15" + ".txt", true)
		try {
			fw.write("FIRST SUB:  " + a + "\n")
			fw.write("SECOND SUB: " + b + "\n")
			val contained = if(a != null && b != null) { a.toList.forall(b.toList.contains) } else { false }
			fw.write("F in S?     " + contained + "\n")
//			print("F in S?     " + contained + "\n")

			if(!contained){
				fw.write("AUXR: " + auxR + "\n")
				fw.write("AUXL: " + auxL + "\n")
				fw.write("SAFE: " + sl + "\n")
				fw.write("RIGHT: " + right + "\n")
				fw.write("LEFT: " + left + "\n")
				fw.write(marked + "\n")


//				print("AUXR: " + auxR + "\n")
//				print("AUXL: " + auxL + "\n")
//				print("SAFE: " + sl + "\n")
//				print("RIGHT: " + right + "\n")
//				print("LEFT: " + left + "\n")
//				print(marked + "\n")        
			}
		}
		finally fw.close() 
	}


	protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
		val edgesToDelete = new FOEdgesToDelete()
		val safeMap = new MMap[SequentProofNode, Sequent]()
		def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
			val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
					//      println("Node: " + p)
					//      println("Safe: " + safeLiterals)

					safeMap.put(p, safeLiterals.toSeqSequent)
					p match {
					  
			  case UnifyingResolution(left, right, auxL, auxR) => {
			    val auxLcheck = checkForResSmart(safeLiterals.suc, auxL, p)
			    val sigmaL = auxLcheck._2 
			    
//			    println("left: " + left)
//			    println("mgu: " + p.asInstanceOf[UnifyingResolution].mgu)
//			    println("safe: " + safeLiterals.ant + "-" + safeLiterals.suc + " should contain " + auxL)
//			    println(" and: " + applySub(left.conclusion, sigmaL))

			      val auxRcheck = checkForResSmart(safeLiterals.ant, auxR, p)
			      val sigmaR = auxRcheck._2 
			      
//			    val auxLfinalCheck = if (auxLcheck._1) { finalCheck(safeLiterals.toSeqSequent, left.conclusion, false) } else { (false, null) }
			    val auxLfinalCheck = if (auxLcheck._1) { finalCheck(safeLiterals.toSeqSequent, applySub(left.conclusion, sigmaL), true) } else { (false, null) }
			    
			    if (auxLcheck._1 && auxLfinalCheck._1 && auxLfinalCheck._2 != null) {
//			      println("marking right " + auxLfinalCheck._2)
			      edgesToDelete.markRightEdge(p)
			    } else {

//			      val auxRfinalCheck = if (auxRcheck._1) { finalCheck(safeLiterals.toSeqSequent, right.conclusion, false) } else { (false, null) }
			      val auxRfinalCheck = if (auxRcheck._1) { finalCheck(safeLiterals.toSeqSequent, applySub(right.conclusion, sigmaR), true) } else { (false, null) }
			      if(auxRcheck._1 && auxRfinalCheck._1 && auxRfinalCheck._2 != null){
//			        println("marking left " + "" + auxRfinalCheck._2)
			        edgesToDelete.markLeftEdge(p)
			      }
			    }
			  }

			  /*
					case UnifyingResolution(left, right, auxL, auxR) if (checkForResSmart(safeLiterals.suc, auxL, p)._1 &&        
							finalCheck(safeLiterals.toSeqSequent, left.conclusion, false)._1) => {
//								val firstSub = checkForResSmart(safeLiterals.suc, auxR, p)._2
//										val secondSub = finalCheck(safeLiterals.toSeqSequent, left.conclusion, false)._2
//										isSubSubstitutionAndPrint(firstSub, secondSub, safeLiterals.toSeqSequent, auxR, auxL, right, left, "MARKING RIGHT")

										//Both are here in test case
										val firstSubB = checkForResSmart(safeLiterals.suc, auxL, p)._2
										val newLeft = Sequent(left.conclusion.ant.map{ x: E => firstSubB(x) }.toSeq: _*)(left.conclusion.suc.map{ x: E => firstSubB(x) }.toSeq: _*)
										println("subB: " + firstSubB)
										println("newLeft: " + newLeft)
										
//										wouldChangeMatter(firstSub, secondSub, safeLiterals.toSeqSequent, auxR, auxL, right, left, "MARKING RIGHT", newLeft.toSeqSequent, firstSubB)


										edgesToDelete.markRightEdge(p)
							}
					case UnifyingResolution(left, right, auxL, auxR) if (checkForResSmart(safeLiterals.ant, auxR, p)._1 &&
							finalCheck(safeLiterals.toSeqSequent, right.conclusion, false)._1) => {
//								val firstSub = checkForResSmart(safeLiterals.ant, auxL, p)._2
//										val secondSub = finalCheck(safeLiterals.toSeqSequent, right.conclusion, false)._2
//										isSubSubstitutionAndPrint(firstSub, secondSub, safeLiterals.toSeqSequent, auxR, auxL, right, left, "MARKING LEFT")
										edgesToDelete.markLeftEdge(p)
							}
							*/

							//          //Debug case
							//        case UnifyingResolution(left, right, auxL, auxR) => {
							////          println("left: " + left)
							////          println("right: " + right)
							////          println("auxL: " + auxL)
							////          println("auxR: " + auxR)
							//          
							//          
							////          println("auxLcheck: " + checkForResSmart(safeLiterals.ant, auxL, p))
							////          println("rightcheck: " + finalCheck(safeLiterals.toSeqSequent, right.conclusion, false))          
							////          println("auxRcheck: " + checkForResSmart(safeLiterals.suc, auxR, p))
							////          println("leftcheck: " + finalCheck(safeLiterals.toSeqSequent, left.conclusion, false))
							//          
							//        }          

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
