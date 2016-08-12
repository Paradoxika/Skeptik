package at.logic.skeptik.proof.sequent
package resolution

import collection.mutable.{ HashMap => MMap, Set => MSet }
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents
import at.logic.skeptik.parser.ProofParserSPASS

class UnifyingResolutionMRR(override val leftPremise: SequentProofNode, override val rightPremise: SequentProofNode,
		override val auxL: E, override val auxR: E, override val leftClean: SequentProofNode, override val overRide: Substitution)(implicit unifiableVariables: MSet[Var])
		extends UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftClean, overRide) {

	override val conclusionContext = {
			val antecedent = leftClean.conclusion.ant.map(e => mgu(e)) ++
					(rightPremise.conclusion.ant.filter(_ != auxR)).map(e => mgu(e))
					val succedent = (leftClean.conclusion.suc.filter(_ != auxL)).map(e => mgu(e)) ++
					rightPremise.conclusion.suc.map(e => mgu(e))
					if (overRide == null) {
						new Sequent(antecedent, succedent)
					} else {
						new Sequent(antecedent.map(e => overRide(e)), succedent.map(e => overRide(e)))
					}

	}

}

object UnifyingResolutionMRR extends CanRenameVariables with FindDesiredSequent {


	def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, desired: Sequent, relaxation: Substitution = null)(implicit unifiableVariables: MSet[Var]) = {

		val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
				val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)
				if (unifiablePairs.length > 0) {
					findDesiredSequent(unifiablePairs, desired, leftPremise, rightPremise, leftPremiseClean, true, relaxation)
				} else if (unifiablePairs.length == 0) {
					throw new MRRException("Resolution (MRR): the conclusions of the given premises are not resolvable.")
				} else {
					//Should never really be reached in this constructor
					throw new MRRException("Resolution (MRR): the resolvent is ambiguous.")
				}
	}


	def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

		val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
				val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)

				if (unifiablePairs.length == 1) {

					val (auxL, auxR) = unifiablePairs(0)
							var ax = null.asInstanceOf[SequentProofNode]
									ax = new UnifyingResolutionMRR(leftPremise, rightPremise, auxL, auxR, leftPremiseClean, null)
					var con = Contraction(ax)(unifiableVariables)
					//If they're ever equal, contraction did nothing; discard the contraction
					while (!con.conclusion.equals(ax.conclusion)) {

						ax = con
								con = Contraction(ax)(unifiableVariables)
					}
					ax
				} else if (unifiablePairs.length == 0) throw new MRRException("Resolution (MRR): the conclusions of the given premises are not resolvable.")
				else throw new MRRException("Resolution (MRR): the resolvent is ambiguous.")
	}

	def apply(premises: List[SequentProofNode], desired: Sequent)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
		//Find the special node
		val repeats = premises.diff(premises.distinct).distinct

				if (repeats.size != 0) {
					throw new MRRException("MRR assumption failed")
				}
		var special = repeats.head

				if (desired.logicalSize != 0) {
					throw new MRRException("MRR assumption failed")
				}
		val others = premises.filterNot(_ eq special)

				for (p <- others) {

					var tryReversed = false;

					try {
						special = UnifyingResolutionMRR(p, special)
					} catch {
					case e: Exception => {
						if (e.getMessage().equals("Resolution (MRR): the resolvent is ambiguous.")) {
							special = fixAmbiguity(p, special)
									tryReversed = false
						} else {
							tryReversed = true
						}
					}
					}

					if (tryReversed) {
						try {
							special = UnifyingResolutionMRR(special, p)
						} catch {
						case e: Exception => {
							if (e.getMessage().equals("Resolution (MRR): the resolvent is ambiguous.")) {
								special = fixAmbiguity(special, p)
							}
						}
						}
					}


				}

		assert(special.conclusion.logicalSize == 0)
		special
	}

	def unapply(p: SequentProofNode) = p match {
	case p: UnifyingResolutionMRR => Some((p.leftPremise, p.rightPremise, p.auxL, p.auxR))
	case _ => None
	}

	def fixAmbiguity(l: SequentProofNode, r: SequentProofNode)(implicit unifibaleVars: MSet[Var]): SequentProofNode = {
		val unifiablePairs = (for (auxL <- l.conclusion.suc; auxR <- r.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)

				val lSize = l.conclusion.suc.size + l.conclusion.ant.size
				val rSize = r.conclusion.suc.size + r.conclusion.ant.size

				//    assert(unifiablePairs.size > 0) //should always be >1 on the initial call
				if (lSize > 1) {
					//l is the special node
					if (l.conclusion.ant.size > 0) {

						val newDesired = addAntecedents(l.conclusion.ant.tail.toList)
								val newRes = UnifyingResolutionMRR(l, r, newDesired)
								fixAmbiguity(newRes, r)
					} else {

						val newDesired = addAntecedents(l.conclusion.suc.tail.toList)
								val newRes = UnifyingResolutionMRR(l, r, newDesired)
								fixAmbiguity(newRes, r)
					}

				} else if (rSize > 1) {
					//r is the special node
					if (r.conclusion.ant.size > 0) {

						val newDesired = addAntecedents(r.conclusion.ant.tail.toList)
								val newRes = UnifyingResolutionMRR(l, r, newDesired)
								fixAmbiguity(l, newRes)
					} else {

						val newDesired = addAntecedents(r.conclusion.suc.tail.toList)
								val newRes = UnifyingResolutionMRR(l, r, newDesired)
								fixAmbiguity(l, newRes)
					}
				} else {
					//base case
					val out = UnifyingResolutionMRR(l, r)
							out
				}
	}
}

case class MRRException(error: String) extends Exception {
	override def getMessage: String = {
	error
}
}

