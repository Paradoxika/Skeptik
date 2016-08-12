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

class FOSubstitution(val premise: SequentProofNode, val sub: Substitution)(implicit unifiableVariables: MSet[Var])
  extends SequentProofNode with Unary with CanRenameVariables with FindsVars with FindDesiredSequent {

  def conclusionContext = conclusion
  def auxFormulas = premise.mainFormulas diff conclusion
  def mainFormulas = conclusion intersect premise.mainFormulas

  override lazy val conclusion = {
    val antecedent = premise.conclusion.ant.map(e => sub(e))
    val succedent = premise.conclusion.suc.map(e => sub(e))
    new Sequent(antecedent, succedent)
  }

  object FOSubstitution {
    def apply(premise: SequentProofNode, sub: Substitution)(implicit unifiableVariables: MSet[Var]) = {
      new FOSubstitution(premise, sub)
    }

    def unapply(p: SequentProofNode) = p match {
      case p: FOSubstitution => Some((p.premise, p.sub))
      case _ => None
    }
  }
}
