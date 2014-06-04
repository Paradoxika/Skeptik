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

  //TODO: define these variables
  def leftAuxFormulas: SeqSequent = ???
  def rightAuxFormulas: SeqSequent = ???

  var isMRR = false

  // When a unifiable variable X occurs in both premises, 
  // we must rename its occurrences in one of the premises to a new variable symbol Y
  // not occurring in any premise
  //TODO: remove these variables?
  val (leftPremiseR: Sequent, rightPremiseR: Sequent, auxLR: E, auxRR: E) = {
    (leftPremise.conclusion, rightPremise.conclusion, auxL, auxR)
  }

  val mgu = unify((auxLR, auxRR) :: Nil) match {
    case None => {
      throw new Exception("Resolution: given premise clauses are not resolvable.")
    }
    case Some(u) => {
      u
    }
  }

  //ALTERNATIVELY: if we have mgu variables appearing ONLY in the left, then just use the contraction
  override val conclusionContext = {

    val leftAntContainsMGU = containsMGUVariables(leftClean.conclusion.ant)
    val rightAntContainsMGU = containsMGUVariables(rightPremise.conclusion.ant)

    val leftSucContainsMGU = containsMGUVariables(leftClean.conclusion.suc)
    val rightSucContainsMGU = containsMGUVariables(rightPremise.conclusion.suc)

    val leftContainsMGU = leftAntContainsMGU || leftSucContainsMGU
    val rightContainsMGU = rightAntContainsMGU || rightSucContainsMGU

    if (leftContainsMGU && rightContainsMGU) {
      //not an MRR instance
    } else if (leftContainsMGU && !rightContainsMGU) {
      //      println("MRR instance!")
      isMRR = true
    } else if (!leftContainsMGU && rightContainsMGU) {
      //      println("MRR instance!")
      isMRR = true
    } //TODO: this is reporting MRR instance on cases where it's not expected to be one. This seems to be luck. 
    //...but would applying contraction in these cases break anything?

    val antecedent = leftClean.conclusion.ant.map(e => mgu(e)) ++
      (rightPremise.conclusion.ant.filter(_ != auxR)).map(e => mgu(e))
    val succedent = (leftClean.conclusion.suc.filter(_ != auxL)).map(e => mgu(e)) ++
      rightPremise.conclusion.suc.map(e => mgu(e))
    new Sequent(antecedent, succedent)
  }

  def containsMGUVariables(s: Seq[E]): Boolean = {
    // println("" + s.map(e => mgu(e)) + "=?=" + s)
    !(s.map(e => mgu(e)).equals(s))
  }
}

object UnifyingResolution {
  //def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, auxL: E, auxR: E)(implicit unifiableVariables: MSet[Var]) = new UnifyingResolution(leftPremise, rightPremise, auxL, auxR)
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {

    val cleanNodes = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
    val leftPremiseClean = cleanNodes._1
    val rightPremiseClean = cleanNodes._2

    def isUnifiable(p: (E, E)) = unify(p :: Nil)(unifiableVariables) match {
      case None => false
      case Some(_) => true
    }
    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)
    if (unifiablePairs.length > 0) {
      val (auxL, auxR) = unifiablePairs(0)
      new UnifyingResolution(leftPremise, rightPremiseClean, auxL, auxR, leftPremiseClean)
    } else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
    else throw new Exception("Resolution: the resolvent is ambiguous.")
  }
  def unapply(p: SequentProofNode) = p match {
    case p: UnifyingResolution => Some((p.leftPremise, p.rightPremise, p.auxL, p.auxR))
    case _ => None
  }

  def fixSharedNoFilter(leftPremiseR: SequentProofNode, rightPremiseR: SequentProofNode, count: Int, unifiableVariables: MSet[Var]): (SequentProofNode, SequentProofNode) = {

    // For example, suppose we are trying to resolve:

    //  p(X) |- q(a)     with    q(X) |- 

    // note that all variables are assumed to be universally quantified.
    // therefore, the X in the left premise has nothing to do with the X in the right premise.

    //check if there is a variable in both  

    def getSetOfVarsFromPremise(pn: SequentProofNode) = {
      val ante = pn.conclusion.ant
      val succ = pn.conclusion.suc

      def investigateExpr(e: E): Set[Var] = e match {
        case App(e1, e2) => {
          investigateExpr(e1).union(investigateExpr(e2))
        }
        case Abs(v, e1) => {
          investigateExpr(v).union(investigateExpr(e1))
        }
        case v: Var => {
          //Only care if the variable is a capital         
          val hasLowerCase = v.name.exists(_.isLower)
          val notAnInt = v.name.charAt(0).isLetter
          if (!hasLowerCase && notAnInt) {
            Set[Var](v)
          } else {
            Set[Var]()
          }
        }
      }

      def getSetOfVarsFromExpr(e: Seq[E]): Set[Var] = {
        if (e.length > 1) {
          investigateExpr(e.head).union(getSetOfVarsFromExpr(e.tail))
        } else if (e.length == 1) {
          investigateExpr(e.head)
        } else {
          Set[Var]()
        }
      }
      getSetOfVarsFromExpr(ante).union(getSetOfVarsFromExpr(succ))
    }

    val sharedVars = getSetOfVarsFromPremise(leftPremiseR).intersect(getSetOfVarsFromPremise(rightPremiseR))

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
      val availableVars = unifiableVariables.diff(sharedVars.union(getSetOfVarsFromPremise(leftPremiseR).union(getSetOfVarsFromPremise(rightPremiseR))))

      var replacement = null.asInstanceOf[Var] //TODO: better way to do this?
      if (availableVars.size >= 1) {
        //use one thats available
        replacement = availableVars.head
      } else {
        replacement = new Var("NEW" + count, i)
        unifiableVariables += new Var("NEW" + count, i)
      }

      val sub = Substitution(sharedVars.head -> replacement) //perform the replacement

      //Substitute the new name into one of the premises; let say the left one //TODO: check: does this matter?

      val newAnt = for (a <- leftPremiseR.conclusion.ant) yield sub(a)
      val newSuc = for (a <- leftPremiseR.conclusion.suc) yield sub(a)

      val sA = addAntecedents(newAnt.toList)
      val sS = addSuccedents(newSuc.toList)

      val seqOut = sS union sA
      val axOut = Axiom(seqOut)

      fixSharedNoFilter(axOut, rightPremiseR, count + 1, unifiableVariables) //recursively call the function so that any more shared variables are also dealt with
    } else { //sharedVars.size  < 1
      (leftPremiseR, rightPremiseR) //no change
    }
  }
}
