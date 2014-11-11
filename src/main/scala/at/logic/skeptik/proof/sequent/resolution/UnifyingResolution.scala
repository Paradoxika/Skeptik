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
  with NoMainFormula with CanRenameVariables {

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

trait FindsVars extends checkUnifiableVariableName {
  def getSetOfVars(e: E*): MSet[Var] =
    if (e.length == 1) {
      e.head match {
        case App(e1, e2) => {
          getSetOfVars(e1).union(getSetOfVars(e2))
        }
        case Abs(v, e1) => {
          getSetOfVars(v).union(getSetOfVars(e1))
        }
        case Var(n, at.logic.skeptik.expression.i) => {
          if (isValidName(Var(n, i))) {
            MSet[Var](Var(n, i))
          } else {
            MSet[Var]()
          }
        }
        case _ => {
          MSet[Var]()
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
}

trait CanRenameVariables extends FindsVars {
  def isUnifiable(p: (E, E))(implicit unifiableVariables: MSet[Var]) = unify(p :: Nil)(unifiableVariables) match {
    case None => false
    case Some(_) => true
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

trait checkUnifiableVariableName {
  def isValidName(v: Var): Boolean = {
    val hasLowerCaseFirst = v.name.charAt(0).isLower
    val notAnInt = v.name.charAt(0).isLetter
    notAnInt && !hasLowerCaseFirst
  }

  //  def isValidNameB(v: Var): Boolean = {
  //    val hasLowerCaseFirst = v.name.charAt(0).isLower
  //    val notAnInt = v.name.charAt(0).isLetter
  //    notAnInt //&& !hasLowerCaseFirst
  //  }
}

trait FindDesiredSequent extends FindsVars with checkUnifiableVariableName with CanRenameVariables {

  def intersectMaps(a: MMap[Var, Set[Var]], b: MMap[Var, Set[Var]]): MMap[Var, Set[Var]] = {
    val out = MMap[Var, Set[Var]]()

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

  def validMap(m: MMap[Var, Set[Var]]): Boolean = {
    for (k <- m.keySet) {
      if (m.get(k).get.size != 1) {
        return false
      }
    }
    true
  }

  def validMapB(m: MMap[Var, Set[Var]], vars: MSet[Var]): Boolean = {
    for (k <- m.keySet) {
      if (vars.contains(k) && m.get(k).get.size != 1) {
        return false
      }
      if (!vars.contains(k) && m.get(k).get.size == 0) {
        return false
      }
    }
    true
  }

  def convertTypes(in: List[(E, E)]): List[(Var, E)] = {
    if (in.length > 0) {
      val h = in.head
      val newH = (h._1.asInstanceOf[Var], h._2)
      List[(Var, E)](newH) ++ convertTypes(in.tail)
    } else {
      List[(Var, E)]()
    }
  }

  def generateSubstitutionOptions(computed: Seq[E], desired: Seq[E]) = {
    val map = new MMap[Var, Set[Var]]()
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

        val u = unify((c, dClean) :: Nil)(cVars union dVars)

        u match {
          case Some(s) => {
            if (checkSubstitutions(s)) {
              //make sure it's just a renaming

              //so that var could have gone to any of the variables in d; add them all
              //NO -- it can only go to what the sub said it could!

              for (cv <- cVars) {

                val sub = inverseSub(getValidSubstitution(s, cv))
                val realVars = getSetOfVars(sub)
                if (map.keySet.contains(cv)) {
                  //update that set
                  map.put(cv, map.get(cv).get ++ realVars)
                } else {
                  //add a new set
                  //note the conversion is safe since checkSubstitutions already confirms it's a var
                  map.put(cv, Set[Var]() ++ realVars)
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

  def checkSubstitutions(s: Substitution): Boolean = {
    for (e <- s.values) {
      e match {
        case Var(name, _) => {
          if (!isValidName(e.asInstanceOf[Var])) {
            return false
          }
        }
        case _ => {
          return false
        }
      }
    }
    true
  }

  def getValidSubstitution(s: Substitution, v: Var): E = {
    for (k <- s.keys) {
      if (k.equals(v)) {
        s.get(k).get match {
          case Var(name, _) => {
            return s.get(k).get
          }
        }

      }
    }
    v
  }

  def unifyClean(c: E, d: E) = {

    val cAxiom = new Axiom(Sequent(c)())
    val dAxiom = new Axiom(Sequent(d)())
    val vars = getSetOfVars(cAxiom) union getSetOfVars(dAxiom)
    val dAxiomClean = fixSharedNoFilter(dAxiom, cAxiom, 0, vars)
    val dClean = dAxiomClean.conclusion.ant.head

    //should never not be able to unify -- one is the other, but with new variable names
    val dToCleanSub = (unify((d, dClean) :: Nil)(vars)).get
    val inverseSubs = dToCleanSub.toMap[Var, E].map(_.swap)
    val inverseSubsCasted = convertTypes(inverseSubs.toList)
    val inverseSub = Substitution(inverseSubsCasted: _*)

    val u = unify((c, dClean) :: Nil)(vars)

    (u, inverseSub)
  }

  def checkHelperAlphaManual(computed: Seq[E], desired: Seq[E])(implicit unifiableVariables: MSet[Var]): Boolean = {
    if (computed.size != desired.size) {
      return false
    } else if (computed.size == 0 && desired.size == 0) {
      return true
    }

    for (f <- computed) {

      for (g <- desired) {
        val u = unify((f, g) :: Nil)
        u match {
          case Some(s) => {
            if (checkSubstitutions(s)) {
              //add current subs to this (not checkSubs is used above! modify with care)
              return checkHelperAlphaManual(computed.filter(!_.equals(f)), desired.filter(!_.equals(g)))
            }
          }
          case None => {
          }
        }
      }

    }
    false
  }

  def checkHalf(computed: Seq[E], desired: Seq[E])(implicit unifiableVariables: MSet[Var]): Boolean = {
    if (computed.size == desired.size) {
      checkHelperAlphaManual(computed, desired)
    } else {
      false
    }
  }

  def desiredFound(computed: Sequent, desired: Sequent)(implicit unifiableVariables: MSet[Var]): Boolean = {
    if (computed == desired) {
      return true
    } else {
      if (computed.logicalSize == desired.logicalSize) {
        if (getSetOfVars(Axiom(computed)).size != getSetOfVars(Axiom(desired)).size) {
          return false
        }

        val commonVars = (getSetOfVars(Axiom(computed.ant)) intersect getSetOfVars(Axiom(computed.suc)))

        val antMap = generateSubstitutionOptions(computed.ant, desired.ant)
        val sucMap = generateSubstitutionOptions(computed.suc, desired.suc)
        val intersectedMap = intersectMaps(antMap, sucMap)

        if (!validMapB(intersectedMap, commonVars)) {
          return false
        }
        if (checkHalf(computed.ant.distinct, desired.ant.distinct)) {
          if (checkHalf(computed.suc.distinct, desired.suc.distinct)) {
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
            try {

              val desiredSequentClean = fixSharedNoFilter(Axiom(desired), ax, 0, unifiableVariables).conclusion

              Contraction(ax, desiredSequentClean)(unifiableVariables)
            } catch {
              case e: Exception => {
                ax //do nothing with this; we can't contract it anyways
              }
            }
          } else {
            ax
          }

        } else {
          new UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftPremiseClean)
        }
      }
      val computedSequent = computedResolution.conclusion.toSeqSequent

      val computedSequentClean = fixSharedNoFilter(Axiom(computedSequent), Axiom(desired), 0, unifiableVariables).conclusion

      if (desiredFound(desired, computedSequentClean)) {
        computedResolution
      } else {
        findDesiredSequent(pairs.tail, desired, leftPremise, rightPremise, leftPremiseClean, isMRR)
      }
    }
  }
}

