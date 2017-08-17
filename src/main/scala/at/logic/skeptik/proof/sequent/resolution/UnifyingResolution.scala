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
                         val auxL: E, val auxR: E, val leftClean: SequentProofNode, val overRide: Substitution)(implicit unifiableVariables: MSet[Var])
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

  //Removes one copy of the formula
  def remove(e: E, list: List[E]) = list diff List(e)

  override val conclusionContext = {
    val antecedent = leftClean.conclusion.ant.map(e => mgu(e)) ++
      remove(auxR, rightPremise.conclusion.ant.toList).map(e => mgu(e))
    val succedent = remove(auxL, leftClean.conclusion.suc.toList).map(e => mgu(e)) ++
      rightPremise.conclusion.suc.map(e => mgu(e))

    if (overRide == null) {
      new Sequent(antecedent, succedent)
    } else {
      new Sequent(antecedent.map(e => overRide(e)), succedent.map(e => overRide(e)))
    }
  }

}

object UnifyingResolution extends CanRenameVariables with FindDesiredSequent {
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, desired: Sequent = null)(implicit unifiableVariables: MSet[Var]) = {
    val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)

    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)
    if (unifiablePairs.length > 0 && desired != null) {
      findDesiredSequent(unifiablePairs, desired, leftPremise, rightPremise, leftPremiseClean, false)
    } else if (unifiablePairs.length == 1) {
      val (auxL, auxR) = unifiablePairs(0)
      new UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftPremiseClean, null)        
      
    } else if (unifiablePairs.length == 0) {
      throw new Exception("Resolution: the conclusions of the given premises are not resolvable. A\nDesired: " + desired + "\nLeft premise: " + leftPremise.toString() + "\nRight premise: " + rightPremise.toString() + "\nVariables: " + unifiableVariables.mkString(","))
    } else {
      throw new Exception("Resolution: the resolvent is ambiguous.\nDesired" + desired + "\nLeft premise: " + leftPremise.toString() + "\nRight premise: " + rightPremise.toString() + "\nVariables: " + unifiableVariables.mkString(","))
    }
  }


  def unapply(p: SequentProofNode) = p match {
    case p: UnifyingResolution => Some((p.leftPremise, p.rightPremise, p.auxL, p.auxR))
    case _                     => None
  }

  def resolve(leftPremise: SequentProofNode, rightPremise: SequentProofNode, desiredSequent: Sequent, unifiableVariables: MSet[Var]) = {
    try {
      apply(leftPremise, rightPremise, desiredSequent)(unifiableVariables)
    } catch {
      case e: Exception =>
        apply(rightPremise, leftPremise, desiredSequent)(unifiableVariables)
    }
  }

  def resolve(leftPremise: SequentProofNode, rightPremise: SequentProofNode, unifiableVariables: MSet[Var]): UnifyingResolution = {
    def applyManagingAmbiguity(leftPremise: SequentProofNode, rightPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {

      val leftPremiseClean = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
      val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)

      if (unifiablePairs.length >= 1) {
        val (auxL, auxR) = unifiablePairs(0)
        new UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftPremiseClean, null)
      } else if (unifiablePairs.length == 0) {
        throw new Exception("Resolution: the conclusions of the given premises are not resolvable. B\nLeft premise: " + leftPremise.toString() + "\nRight premise: " + rightPremise.toString() + "\nVariables: " + unifiableVariables.mkString(","))
      } else {
        throw new Exception("Resolution: the resolvent is ambiguous.\nLeft premise: " + leftPremise.toString() + "\nRight premise: " + rightPremise.toString() + "\nVariables: " + unifiableVariables.mkString(","))
      }
    }
    try {
      applyManagingAmbiguity(leftPremise, rightPremise)(unifiableVariables)
    } catch {
      case e: Exception =>
        applyManagingAmbiguity(rightPremise, leftPremise)(unifiableVariables)
    }
  }
}

trait FindMGU extends FindDesiredSequent {
  def getRenamedMGU(original: Sequent, clean: Sequent, sub: Substitution, vars: MSet[Var]): Substitution = {
    val renamingForward = findRenaming(original, clean)(vars)
    if (renamingForward.size == 0) {
      return sub
    }

    val renamingBackward = findRenaming(clean, original)(vars)

    def appSub(pair: (Var, E)): (Var, E) = {
      if (!renamingForward.get(pair._1).isEmpty) {
        (renamingForward(pair._1).asInstanceOf[Var], pair._2)
      } else if (!renamingBackward.get(pair._1).isEmpty) {
        (renamingBackward(pair._1).asInstanceOf[Var], pair._2)
      } else {
        pair
      }

    }
    val outPairs = sub.toList.map(p => appSub(p))

    Substitution(outPairs: _*)
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

  def getSetOfVars(seq: Sequent): MSet[Var] = {
    val ante = seq.ant
    val succ = seq.suc

    getSetOfVars(ante: _*).union(getSetOfVars(succ: _*))
  }  
  
  def getSetOfVars(pn: SequentProofNode): MSet[Var] = {
    getSetOfVars(pn.conclusion)
  }
}

trait CanRenameVariables extends FindsVars {

  def applySub(seq: Sequent, sub: Substitution, distinctOnly: Boolean = false): Sequent = {
    if(seq == null) { return null }
    if(sub == null) { return seq }
    
    val newAnt = for (a <- seq.ant) yield sub(a)
    val newSuc = for (a <- seq.suc) yield sub(a)
    
    
    val sA = if(distinctOnly){
      addAntecedents(newAnt.toList.distinct)
    } else {
      addAntecedents(newAnt.toList)
    }
    val sS = if(distinctOnly){
        addSuccedents(newSuc.toList.distinct)
      } else {
        addSuccedents(newSuc.toList)
      }

    val newComputed = sS union sA
    newComputed
  }

  def occurCheck(p: (E, E), u: Substitution): Boolean = {
    for (sp <- u.toList) {
      val v = sp._1
      val e = sp._2
      if (!e.isInstanceOf[Var]) {
        if (getSetOfVars(e) contains v) {
          return false
        }
      }
    }
    true
  }

  def isUnifiable(p: (E, E))(implicit unifiableVariables: MSet[Var]) = unify(p :: Nil)(unifiableVariables) match {
    case None => false
    case Some(u) => {
      occurCheck(p, u)
    }
  }

  def getUnifier(p: (E, E))(implicit unifiableVariables: MSet[Var]): Substitution = unify(p :: Nil)(unifiableVariables) match {
    case None => null
    case Some(u) => {
      if (occurCheck(p, u)) {
        u
      } else {
        null
      }
    }
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
      val seqOut = applySub(leftPremiseR.conclusion, sub)

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

}

trait FindDesiredSequent extends FindsVars with checkUnifiableVariableName with CanRenameVariables {

  def contractIfHelpful(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {
    val con = Contraction(premise)(unifiableVariables)
    if (con.conclusion.size < premise.conclusion.size) {
//      println("contraction was helpful to get: " + con)
      con
    } else {
      premise
    }
  }

  def intersectMaps(a: MMap[Var, Set[E]], b: MMap[Var, Set[E]]): MMap[Var, Set[E]] = {
    val out = MMap[Var, Set[E]]()

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

  def validMap(m: MMap[Var, Set[E]], vars: MSet[Var]): Boolean = {
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


  def generateSubstitutionOptions(computed: Seq[E], desired: Seq[E], vars: MSet[Var] = null, requireOnlyRenamings: Boolean = false) = {
    val map = new MMap[Var, Set[E]]()
    for (c <- computed) {
      var cVars = getSetOfVars(c)
      for (d <- desired) {
        val dVars = getSetOfVars(d)

        val cAxiom = new Axiom(Sequent(c)())
        val dAxiom = new Axiom(Sequent(d)())
        val dAxiomClean = fixSharedNoFilter(dAxiom, cAxiom, 0, cVars union dVars)
        val dClean = dAxiomClean.conclusion.ant.head

        val u = if (vars == null) { unify((c, dClean) :: Nil)(cVars union dVars) } else { unify((c, dClean) :: Nil)(vars) }
        if (vars != null) { cVars = vars }

        u match {
          case Some(s) => {
            val allRenamings = checkSubstitutions(s)
            if(!requireOnlyRenamings || (requireOnlyRenamings && allRenamings)){
            for (cv <- cVars) {

              if (map.keySet.contains(cv)) {
                //update that set
                def sub = u.get
                def entry = sub.get(cv)
                if (!entry.isEmpty) {
                  map.put(cv, map.get(cv).get ++ entry)
                }
              } else {
                //add a new set
                //note the conversion is safe since checkSubstitutions already confirms it's a var
                def sub = u.get
                def entry = sub.get(cv)
                if (!entry.isEmpty) {
                  map.put(cv, Set[Var]() ++ entry)
                }
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
          case _ => {
            return s.get(k).get
          }
        }

      }
    }
    v
  }

  def checkMapSub(m: MMap[Var, Set[E]], vars: MSet[Var], computed: Sequent, desired: Sequent): (Boolean, Substitution) = {
    //apply to sub
    val newComputed = applyUniqueSubstitutions(m, vars, computed)
    val finalCheck = newComputed.ant.toSet.subsetOf(desired.ant.toSet) && newComputed.suc.toSet.subsetOf(desired.suc.toSet)
    (finalCheck, getUniqueSubstitutions(m, vars))

  }

  def checkSubsetOrEquality(subsetOnly: Boolean, computed: Sequent, desired: Sequent): Boolean = {
    if (subsetOnly) {
      computed.ant.toSet.subsetOf(desired.ant.toSet) && computed.suc.toSet.subsetOf(desired.suc.toSet)
    } else {
      checkIfConclusionsAreEqual(computed, desired)
    }
  }

  def applyUniqueSubstitutions(m: MMap[Var, Set[E]], vars: MSet[Var], computed: Sequent): Sequent = {
    val sub = getUniqueSubstitutions(m, vars)

    //apply to sub
    val newComputed = applySub(computed, sub)
    newComputed
  }

  def computeIntersectedMap(computed: Sequent, desired: Sequent, vars: MSet[Var], allowSubset: Boolean): (Boolean, MMap[Var, Set[E]]) = {
    val cVars = vars
    val antMap = generateSubstitutionOptions(computed.ant, desired.ant, cVars)

    if (!allowSubset && getSetOfVars(computed.ant: _*).size > 0 && antMap.size == 0) {
      return (false, MMap[Var, Set[E]]())
    }

    val sucMap = generateSubstitutionOptions(computed.suc, desired.suc, cVars)
    if (!allowSubset && getSetOfVars(computed.suc: _*).size > 0 && sucMap.size == 0) {
      return (false, MMap[Var, Set[E]]())
    }
    val intersectedMap = intersectMaps(antMap, sucMap)
    if (!validMap(intersectedMap, cVars)) {
      return (false, intersectedMap)
    }
    (true, intersectedMap)
  }

  def findFirstLargeSet(map: MMap[Var, Set[E]], vars: MSet[Var]): Option[Var] = {
    if (map.size == 0) {
      return None
    }
    if (map.head._2.size > 0 && vars.contains(map.head._1)) {
      return Some(map.head._1)
    } else {
      return findFirstLargeSet(map.tail, vars)
    }
  }

  def getUniqueSubstitutions(m: MMap[Var, Set[E]], vars: MSet[Var]): Substitution = {
    var pairs = List[(Var, E)]()
    for (k <- m.keySet) {
      if (m.get(k).get.size == 1 && vars.contains(k)) {
        pairs = pairs ++ List[(Var, E)]((k, m.get(k).get.head))
      }
    }
    val sub = Substitution(pairs: _*)

    sub
  }

  def checkInvalidMapAndReturnSub(m: MMap[Var, Set[E]], vars: MSet[Var], computed: Sequent, desired: Sequent, containmentOnly: Boolean): Substitution = {

//    println("invalid map: " + computed)
//    println("             " + desired)
//    println("c' : " + computed)
    
//    println("m: " + m)
    
    //println("vars: " + vars)
    
    //Check if map is valid: 

    val subsetContainedOrEquals = checkSubsetOrEquality(containmentOnly, computed, desired)

    if (validMap(m, vars) && subsetContainedOrEquals) {
      //get the sub
      val sub = getUniqueSubstitutions(m, vars)

      return sub
    }

    //apply to sub
    val newComputed = applyUniqueSubstitutions(m, vars, computed)
//    println("newComputed: " + newComputed)
    if (checkSubsetOrEquality(containmentOnly, newComputed, desired)) {
      return getUniqueSubstitutions(m, getSetOfVars(Axiom(newComputed)))
    }

    //recurse on the rest
    //Find one variable to recurse on.		
    val bigSetKey = findFirstLargeSet(m, vars)

    val bigSet = bigSetKey match {
      case Some(bigKey) => {
        if (vars.contains(bigKey)) {
          m.get(bigKey).get
        } else {
          Set[Var]()
        }
      }
      case None => {
        Set[Var]()
      }
    }
    
//    println(bigSet)
    for (mVal <- bigSet) {
      val replacement = (bigSetKey.get, mVal)
      val newNewComputed = applySub(newComputed, Substitution(replacement))
      
      val (mapValid, newMap) = computeIntersectedMap(newNewComputed, desired, vars, false)

      val subsetOrEqualityVerified = checkSubsetOrEquality(containmentOnly, newNewComputed, desired)
      val mapValidAndCorrect = subsetOrEqualityVerified && mapValid

      if (mapValidAndCorrect) {
        return Substitution((bigSetKey.get, mVal))
      } else {
        val badVars = getSetOfVars(mVal) ++ MSet[Var](bigSetKey.get)
        val newSetOfVars = vars -- badVars

        val recursiveMap = m - bigSetKey.get

        val rVal = checkInvalidMapAndReturnSub(recursiveMap, newSetOfVars, newNewComputed, desired, containmentOnly)
        if (rVal != null) {
          val newList = rVal.toList ++ List[(Var, E)]((bigSetKey.get, mVal))
          return Substitution(newList: _*)
        }
      }
    }

    //If we got here, there were no recursive calls
    null
  }

  //TODO: remove one of these.
  def checkInvalidMap(m: MMap[Var, Set[E]], vars: MSet[Var], computed: Sequent, desired: Sequent, containmentOnly: Boolean = false): Boolean = {
    return checkInvalidMapAndReturnSub(m, vars, computed, desired, containmentOnly) != null
  }

  def checkInvalidMapB(m: MMap[Var, Set[E]], vars: MSet[Var], computed: Sequent, desired: Sequent, containmentOnly: Boolean = false): Substitution = {
    return checkInvalidMapAndReturnSub(m, vars, computed, desired, containmentOnly)
  }  
  
  def checkIfConclusionsAreEqual(x: SequentProofNode, y: SequentProofNode): Boolean = {
    return checkIfConclusionsAreEqual(x.conclusion, y.conclusion)
  }

  def checkIfConclusionsAreEqual(x: Sequent, y: Sequent): Boolean = {
    val a = y.ant.toSet.subsetOf(x.ant.toSet) && y.suc.toSet.subsetOf(x.suc.toSet)
    val b = x.ant.toSet.subsetOf(y.ant.toSet) && x.suc.toSet.subsetOf(y.suc.toSet)
    return a && b
  }

  def checkRenamingSubstitution(s: Substitution): Substitution = {
    if (s == null) {
      return s
    }
    for (sub <- s) {
      val a = sub._1
      val b = sub._2
      b match {
        case v: Var => {
          if (!isValidName(v)) {
            return null
          }
        }
        case _ => {
          return null
        }
      }
    }

    return s
  }

  def findRenaming(computed: SequentProofNode, desired: SequentProofNode)(implicit unifiableVariables: MSet[Var]): Substitution = {
    return findRenaming(computed.conclusion, desired.conclusion) 
  }

  
  def fastFindRenaming(computed: Sequent, desired: Sequent, strictRenaming: Boolean): Substitution = {
    if(checkIfConclusionsAreEqual(computed, desired)) { return Substitution() }
    if(computed.ant.size != desired.ant.size || computed.suc.size != desired.suc.size){
      return null
    }
    val pairs = MSet[(E,E)]()
    for(ca <- computed.ant){
      for(da <- desired.ant) {
        pairs.add((ca,da))
      }
    }
    for(cs <- computed.suc){
      for(ds <- desired.suc) {
        pairs.add((cs,ds))
      }
    }  
    val cVars = getSetOfVars(Axiom(computed))
    val sigma = unify(pairs.toList)(cVars)
    sigma match {
      case Some(sub) => {
        if(strictRenaming){
          if(checkSubstitutions(sub)){
            sub
          } else {
            null
          } 
        } else {
          sub
        }
      }
      case None => { null }
    }
  }
  
  def findRenaming(computed: Sequent, desired: Sequent)(implicit unifiableVariables: MSet[Var]): Substitution = {
//    val computedClean = fixSharedNoFilter(Axiom(computed), Axiom(desired),0, unifiableVariables).conclusion
//    val ap =  fastFindRenaming(computedClean, desired, true) //Does not work when source literals can match to more than one target
//    val out = if(ap == null) { findRenamingSlow(computed, desired)(unifiableVariables) } else { ap }
//    return out
//    println("c: " + computed)
//    println("d: " + desired)
    findRenamingSlow(computed, desired)(unifiableVariables)
  }
  
  
  
  def findRenamingSlow(computed: Sequent, desired: Sequent, checkMoreGeneral: Boolean = false)(implicit unifiableVariables: MSet[Var]): Substitution = {
    if (checkIfConclusionsAreEqual(computed, desired)) {
      return Substitution()
    } else {
      if (computed.logicalSize == desired.logicalSize) {
        val computedClean = fixSharedNoFilter(Axiom(computed), Axiom(desired), 0, unifiableVariables)

//          println("entering from findRenamingSlow")
//          println("cc: " + computedClean)
//          println(" c: " + computed)
//          
//          println(" d: " + desired)        
        
        //Note that this no longer assumes the sequents have no common variables!
        val antMap = generateSubstitutionOptions(computedClean.conclusion.ant, desired.ant,null,true)
        val sucMap = generateSubstitutionOptions(computedClean.conclusion.suc, desired.suc,null,true)

        val intersectedMap = intersectMaps(antMap, sucMap)
        val computedVars = getSetOfVars(computedClean)
        if (!validMap(intersectedMap, computedVars)) {
//          println("entering from findRenamingSlow")
//          println("cc: " + computedClean)
//          println(" c: " + computed)
//          
//          println(" d: " + desired)
//          println("C " + computedVars + " map: " + intersectedMap)
          val invalidOut = checkInvalidMapAndReturnSub(intersectedMap, computedVars, computedClean.conclusion, desired, false)
          return checkRenamingSubstitution(invalidOut)
        }

        val uniqueSubs = getUniqueSubstitutions(intersectedMap, computedVars)
        val sub = if(!checkMoreGeneral) { 
//          println("A")
          checkRenamingSubstitution(getUniqueSubstitutions(intersectedMap, computedVars)) }
        else {
//          println("B")
          uniqueSubs
        }
        val out = if (sub == null) { sub } else {
          val newComputed = applySub(computedClean.conclusion, sub)
          val matches = newComputed.ant.toSet.subsetOf(desired.ant.toSet) && newComputed.suc.toSet.subsetOf(desired.suc.toSet)
          if (matches) {
            sub
          } else {
            null
          }
        }

        return out
      }
      null
    }
  }

  def findDesiredSequent(pairs: Seq[(E, E)], desired: Sequent, leftPremise: SequentProofNode,
                         rightPremise: SequentProofNode, leftPremiseClean: SequentProofNode, isMRR: Boolean, relaxation: Substitution = null)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    if (pairs.length == 0) {
//      println("desired:   " + desired)
//      println("leftClean: " + leftPremiseClean)
//      println("right:     " + rightPremise)
      throw new Exception("Resolution: Cannot find desired resolvent")
    } else {

      val (auxL, auxR) = pairs(0)
      val computedResolution = {
        if (isMRR) {
          var ax = null.asInstanceOf[SequentProofNode]
          ax = new UnifyingResolutionMRR(leftPremise, rightPremise, auxL, auxR, leftPremiseClean, relaxation)

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
          new UnifyingResolution(leftPremise, rightPremise, auxL, auxR, leftPremiseClean, null)
        }
      }
      val computedSequent = computedResolution.conclusion.toSeqSequent

      //July 28 - this CANNOT change.
      val computedSequentClean = fixSharedNoFilter(Axiom(computedSequent), Axiom(desired), 0, unifiableVariables).conclusion

      var desiredEquivToComputedRelaxed = false
      var computedCleanIsMoreGeneral = false
      if (relaxation != null) {
        val computedSequentRelaxed = applySub(computedSequentClean, relaxation, true)

        //July 28 - changed order of arguments for findRenaming; they should not change
        desiredEquivToComputedRelaxed = findRenaming(computedSequentRelaxed, desired) != null
        computedCleanIsMoreGeneral = isMoreGeneral(computedSequentClean, desired)
      }

      var contractionWorked = false

      try {
        val tryContraction = Contraction(Axiom(computedSequentClean), desired)
        //If we got here, Contraction did not fail a requirement, so the desired was found.
        contractionWorked = true
      } catch {
        case _: Throwable => {
          //do nothing
        }
      }

      //July 28 - changed order of arguments for findRenaming      
      val found = (findRenaming(computedSequentClean, desired) != null) || contractionWorked || desiredEquivToComputedRelaxed || computedCleanIsMoreGeneral

      if (found) {
        computedResolution
      } else {
        findDesiredSequent(pairs.tail, desired, leftPremise, rightPremise, leftPremiseClean, isMRR, relaxation)
      }
    }
  }

  def isMoreGeneral(a: Sequent, b: Sequent)(implicit unifiableVars: MSet[Var]): Boolean = {
    findRenamingSlow(a,b,true) != null
  }

  
  
}

