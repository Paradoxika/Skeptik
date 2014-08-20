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

class UnifyingResolution(val leftPremise: SequentProofNode, val rightPremise: SequentProofNode,
  val auxL: E, val auxR: E, val leftClean: SequentProofNode)(implicit unifiableVariables: MSet[Var])
  extends SequentProofNode with Binary
  with NoMainFormula {

  def leftAuxFormulas: SeqSequent = Sequent()(auxL)
  def rightAuxFormulas: SeqSequent = Sequent(auxR)()

  // When a unifiable variable X occurs in both premises, 
  // we must rename its occurrences in one of the premises to a new variable symbol Y
  // not occurring in any premise

  val mgu = unify((auxL, auxR) :: Nil) match {
    case None => {
      throw new Exception("Resolution: given premise clauses are not resolvable.")
    }
    case Some(u) => {
      u
    }
  }

  override val conclusionContext = {
    val antecedent = leftClean.conclusion.ant.map(e => mgu(e)) ++
      (rightPremise.conclusion.ant.filter(_ != auxR)).map(e => mgu(e))
    val succedent = (leftClean.conclusion.suc.filter(_ != auxL)).map(e => mgu(e)) ++
      rightPremise.conclusion.suc.map(e => mgu(e))
    new Sequent(antecedent, succedent)
  }

}

object UnifyingResolution extends CanRenameVariables with FindDesiredSequent {
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, desired: Sequent)(implicit unifiableVariables: MSet[Var]) = {

    val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)

    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)
    
    if (unifiablePairs.length > 0) {
      findDesiredSequent(unifiablePairs, desired, leftPremise, rightPremise, leftPremiseClean, false)
    } else if (unifiablePairs.length == 0) {
      throw new Exception("Resolution: the conclusions of the given premises are not resolvable. A")
    } else {
      //Should never really be reached in this constructor
      throw new Exception("Resolution: the resolvent is ambiguous.")
    }
  }

  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {

    val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)

    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)

    if (unifiablePairs.length == 1) {
      val (auxL, auxR) = unifiablePairs(0)
      new UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftPremiseClean)
    } else if (unifiablePairs.length == 0) {
      throw new Exception("Resolution: the conclusions of the given premises are not resolvable. B")
    } else {
      throw new Exception("Resolution: the resolvent is ambiguous.")
    }
  }
  def unapply(p: SequentProofNode) = p match {
    case p: UnifyingResolution => Some((p.leftPremise, p.rightPremise, p.auxL, p.auxR))
    case _ => None
  }

}

trait CanRenameVariables {
  def isUnifiable(p: (E, E))(implicit unifiableVariables: MSet[Var]) = unify(p :: Nil)(unifiableVariables) match {
    case None => false
    case Some(_) => true
  }

  def getSetOfVars(e: E*): MSet[Var] =
    if (e.length == 1) {
      e.head match {
        case App(e1, e2) => {
          getSetOfVars(e1).union(getSetOfVars(e2))
        }
        case Abs(v, e1) => {
          getSetOfVars(v).union(getSetOfVars(e1))
        }
        case v: Var => {
          //Only care if the variable starts with a capital         
          val hasLowerCaseFirst = v.name.charAt(0).isLower
          val notAnInt = v.name.charAt(0).isLetter
          if (!hasLowerCaseFirst && notAnInt) {
            MSet[Var](v)
          } else {
            MSet[Var]()
          }
        }

      }
    } else if (e.length > 1) {
      getSetOfVars(e.head).union(getSetOfVars(e.tail: _*))
    } else {
      MSet[Var]()
    }

  def getSetOfVars(pn: SequentProofNode): MSet[Var] = {
    val ante = pn.conclusion.ant
    val succ = pn.conclusion.suc

    getSetOfVars(ante: _*).union(getSetOfVars(succ: _*))
  }

  def fixSharedNoFilter(leftPremiseR: SequentProofNode, rightPremiseR: SequentProofNode, count: Int, unifiableVariables: MSet[Var]): SequentProofNode = {

    // For example, suppose we are trying to resolve:

    //  p(X) |- q(a)     with    q(X) |- 

    // note that all variables are assumed to be universally quantified.
    // therefore, the X in the left premise has nothing to do with the X in the right premise.

    //check if there is a variable in both  

    val sharedVars = getSetOfVars(leftPremiseR).intersect(getSetOfVars(rightPremiseR))

    // if we just resolve these two clauses we would get the following WRONG resolvent:

    // p(a) |- 

    // As a preprocessing step, it is necessary to rename the X's in one of the clauses to a variable symbol 
    // not occurring in any of the premises. For example:

    // p(Y) |- q(a)     with     q(X) |- 

    // Then we get the CORRECT resolvent:

    // p(Y) |- 

    // note that you must add the new symbol Y to the set of unifiable variables, if it is not already there.

    // to avoid the proliferation of new symbols, which could lead to memory issues, 
    // I recommend that you try to use symbols that are already in unifiableVariables (but not in any of the premises)
    // as much as possible.

    // In order to find the variables X that occur in both premises, 
    // I recommend that you create a function that will traverse a formula and return a set of its unifying variables.
    // then you take the intersection of the sets from each premise.

    // In order to replace a variable X by a new variable Y, you can use the existing code for substitutions in the 
    // at.logic.skeptik.expression.substitution.{mutable,immutable} packages. 
    // You can learn how to use substitutions by looking at the MartelliMontanari.

    // By the way, the substitution code is a good example of how you can traverse a formula using Scala's pattern matching.

    if (sharedVars.size > 0) {
      //Find, and assign a new name
      //first diff is so that we don't use a variable that is shared
      //second/third diff is so that we don't use a variable appearing in the formula already
      val availableVars = unifiableVariables.diff(sharedVars.union(getSetOfVars(leftPremiseR).union(getSetOfVars(rightPremiseR))))

      def incrementCounter(start: Int): Int = {
        if (unifiableVariables.contains(new Var("NEW" + start, i))) {
          incrementCounter(start + 1)
        } else {
          start
        }
      }

      val kvs = for (v <- sharedVars) yield {
        val replacement = availableVars.headOption getOrElse {
          val newVar = new Var("NEW" + incrementCounter(count), i)
          unifiableVariables += newVar
          newVar
        } // get a suitable variable from availableVars (must be a different Var in each iteration of this loop) or create a new one...

        if (availableVars.contains(replacement)) { availableVars.remove(replacement) }
        (v -> replacement)
      }

      val sub = Substitution(kvs.toSeq: _*)

      //Substitute the new name into one of the premises; let say the left one 

      val newAnt = for (a <- leftPremiseR.conclusion.ant) yield sub(a)
      val newSuc = for (a <- leftPremiseR.conclusion.suc) yield sub(a)

      val sA = addAntecedents(newAnt.toList)
      val sS = addSuccedents(newSuc.toList)

      val seqOut = sS union sA
      val axOut = Axiom(seqOut)

      axOut
    } else { //sharedVars.size  < 1
      leftPremiseR //no change
    }
  }
}

trait FindDesiredSequent {

  def checkHalf(computed: Seq[E], desired: Seq[E])(implicit unifiableVariables: MSet[Var]): Boolean = {
    if (computed.size == desired.size) {
      var matched = false;
      if (computed.size == 0) {
        matched = true
      }
      //make sure each computed is in the desired
      for (f <- computed) {
        matched = false
        for (g <- desired) {
          val u = unify((f, g) :: Nil)
          u match {
            case Some(_) => matched = true
            case None => {
              matched = matched
            }
          }
        }
        if (!matched) {
          return false
        }
      }
      //make sure each desired is in the computed
      for (g <- desired) {
        matched = false
        for (f <- computed) {
          val u = unify((f, g) :: Nil)
          u match {
            case Some(_) => matched = true
            case None => {
              matched = matched
            }
          }
        }
        if (!matched) {
          return false
        }
      }
      matched
    } else {
      false
    }
  }

  def desiredFound(computed: Sequent, desired: Sequent)(implicit unifiableVariables: MSet[Var]): Boolean = {
    if (computed == desired) {
      return true
    } else {
      if (computed.logicalSize == desired.logicalSize) {
        if (checkHalf(computed.ant, desired.ant)) {

          if (checkHalf(computed.suc, desired.suc)) {

            return true
          }
        }
      }
      false
    }
  }

  def findDesiredSequent(pairs: Seq[(E, E)], desired: Sequent, leftPremise: SequentProofNode,
    rightPremise: SequentProofNode, leftPremiseClean: SequentProofNode, isMRR: Boolean)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

    if (pairs.length == 0) {
      throw new Exception("Resolution: Cannot find desired resolvent")
    } else {
      val (auxL, auxR) = pairs(0)
      val computedResolution = {
        if (isMRR) {
          var ax = null.asInstanceOf[SequentProofNode]
          ax = new UnifyingResolutionMRR(leftPremise, rightPremise, auxL, auxR, leftPremiseClean)

          if (desired.logicalSize < ax.conclusion.logicalSize) {
            Contraction(ax, desired)(unifiableVariables)
          } else {
            ax
          }
        } else {
          new UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftPremiseClean)
        }
      }

      val computedSequent = computedResolution.conclusion.toSeqSequent

      if (desiredFound(desired, computedSequent)) {
        computedResolution
      } else {
        findDesiredSequent(pairs.tail, desired, leftPremise, rightPremise, leftPremiseClean, isMRR)
      }
    }
  }
}

