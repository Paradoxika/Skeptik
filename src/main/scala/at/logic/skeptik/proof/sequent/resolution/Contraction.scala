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

class Contraction(val premise: SequentProofNode, val newAnt: Seq[E])(implicit unifiableVariables: MSet[Var])
extends SequentProofNode with Unary
with NoMainFormula {

	//TODO: define this?
	def auxFormulas = ???

			override val conclusionContext = {
			val antecedent = newAnt
					val succedent = premise.conclusion.suc
					new Sequent(antecedent, succedent)
	}
}

object Contraction {
	def apply(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {
		new Contraction(premise, contract(premise)(unifiableVariables))
	}

	def contract(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): Seq[E] = {
		//Want to do pair-wise comparison for formulas in the antecedent of the premise
		//TODO: also the succedent?
		val ant = premise.conclusion.ant

				//    var change = null.asInstanceOf[List[Substitution]]

				//Check if the current head matches the rest of the antecedent
				def checkHead(h: E, t: Seq[E], start: Int): (Boolean, Int) = {
			if (t.length == 0) {
				return (false, -1)
			} else {
				val matched = contractPair(h, t.head,unifiableVariables)

						if (matched) {
							//          change = replacements
							(true, start)
						} else {
							checkHead(h, t.tail, start + 1)
						}
			}
		}

		def checkAllPairs(ant: Seq[E], start: Int): (Boolean, Int, Int) = {
			if (ant.length == 0) {
				return (false, -1, -1)
			}
			val h = ant.head
					//If the head did not match anything else, check the rest
					val result = checkHead(h, ant.tail, start + 1)
					if (!result._1) {
						checkAllPairs(ant.tail, start + 1)

						//if it did, we found a match, return true.
					} else {
						return (true, start, result._2)
					}
		}

		val temp = checkAllPairs(ant, 0)

				//Remove one of the ones we need to contract
				def removeNth(ant: Seq[E], n: Int, step: Int): List[E] = {
			if (n == step) {
				(ant.tail).toList
			} else {
				List(ant.head) ++ removeNth(ant.tail, n, step + 1)
			}
		}

		if (temp._3 != -1) {
			removeNth(premise.conclusion.ant, temp._3, 0).toSeq
		} else {
			premise.conclusion.ant
		}

	}

  def contractPair(f1: E, f2: E, vars: MSet[Var]): Boolean = { //} f1 match {
    def isUnifiable(p: (E, E)) = unify(p :: Nil)(vars) match {
      case None => false
      case Some(_) => true
    }
    isUnifiable((f1, f2))
  }
}
