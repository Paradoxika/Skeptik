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

class Contraction(val premise: SequentProofNode, val desired: Sequent)(implicit unifiableVariables: MSet[Var])
  extends SequentProofNode with Unary with CanRenameVariables with FindsVars with FindDesiredSequent {

  def conclusionContext = conclusion
  def auxFormulas = premise.mainFormulas diff conclusion
  def mainFormulas = conclusion intersect premise.mainFormulas

  val contraction = checkOrContract(premise.conclusion, desired)(unifiableVariables)

  def newAnt = contraction._1
  def newSuc = contraction._2

  def subs = contraction._3

  override lazy val conclusion = {
    val antecedent = newAnt
    val succedent = newSuc
    new Sequent(antecedent, succedent)
  }

  def checkOrContract(premise: Sequent, desired: Sequent)(implicit unifiableVariables: MSet[Var]): (Seq[E], Seq[E], List[Substitution]) = {
    if (premise.logicalSize > 0) {
      require(premise.logicalSize > desired.logicalSize)
    }

    if (desired.logicalSize == 0) {
      contract(premise, null)
    } else {
      val premiseDistinct = addAntecedents(premise.ant.distinct.toList) union addSuccedents(premise.suc.distinct.toList)
      val desiredDistinct = addAntecedents(desired.ant.distinct.toList) union addSuccedents(desired.suc.distinct.toList)
      if (findRenaming(premiseDistinct, desiredDistinct) == null) {
        desiredIsSafe(premise, desired) //the 'require' is in this call, eventually.
      }
      (desired.ant, desired.suc, null)
    }
  }

  def desiredIsSafe(premise: Sequent, desired: Sequent)(implicit unifiableVariables: MSet[Var]) = {

    val sucMaps = getMaps(premise.suc, desired.suc)
    val antMaps = getMaps(premise.ant, desired.ant)

    val allMaps = antMaps ++ sucMaps
    val finalMerge = buildMap(allMaps, desired)

  }

  def getMaps(premiseHalf: Seq[E], desiredHalf: Seq[E]): Seq[Seq[Substitution]] = {

    val allSubs = for {

      premiseLiteral <- premiseHalf

      instances = for {
        desiredLiteral <- desiredHalf
        unifier = unify((desiredLiteral, premiseLiteral) :: Nil)

        if !unifier.isEmpty
      } yield (desiredLiteral, unifier.get)

      if (checkEmpty(instances, premiseLiteral, desiredHalf))

      subs = for {
        pair <- instances
        if (pair._2.size > 0)
      } yield pair._2

      if (subs.length > 0)

    } yield subs
    allSubs
  }

  //If no unifier was found, this exact literal had better be in the relevant half of the desired sequent
  //note that if the literal IS contained, an empty substitution is returned before we get here
  //but this is still required as I can't put a require statement in a for loop
  def checkEmpty(instances: Seq[(E, Substitution)], literal: E, desiredHalf: Seq[E]): Boolean = {
    if (instances.length == 0) {
      require(desiredHalf.contains(literal))
    }
    //always return true here; note that if the requirement fails, we won't get here anyways
    true
  }

  def buildMap(subs: Seq[Seq[Substitution]], desired: Sequent) = {
    val listOfMaps = for {
      subList <- subs
      tempMap = makeSubMap(subList)
    } yield tempMap
    mergeMaps(listOfMaps, desired)
  }

  def isNotUsed(v: Var, seq: Sequent): Boolean = {
    val seqVars = getSetOfVars(seq.ant: _*) union getSetOfVars(seq.suc: _*)
    return seqVars.contains(v)
  }

  def mergeMaps(listOfMaps: Seq[MMap[Var, Set[E]]], desired: Sequent) = {
    val finalMap = MMap[Var, Set[E]]()
    for (tempMap <- listOfMaps) {
      for (key <- tempMap.keySet) {
        if (finalMap.keySet.contains(key)) {
          val currentSubs = finalMap.get(key).get
          val newSubs = tempMap.get(key).get
          val intersection = currentSubs.intersect(newSubs)
          require(intersection.size > 0 || isNotUsed(key, desired))
          finalMap.update(key, intersection)
        } else {
          finalMap.put(key, tempMap.get(key).get)
        }
      }
    }
    finalMap
  }

  def makeSubMap(subList: Seq[Substitution]) = {
    val tempMap = MMap[Var, Set[E]]()
    for (sub <- subList) {
      for (replacement <- sub) {
        val newExprSet = tempMap.getOrElse(replacement._1, Set[E]()).union(Set[E](replacement._2))
        tempMap.update(replacement._1, newExprSet)
      }
    }
    tempMap
  }

  def contract(seq: Sequent, subs: List[Substitution])(implicit unifiableVariables: MSet[Var]): (Seq[E], Seq[E], List[Substitution]) = {
    def occurCheck(p: (E, E), u: Substitution): Boolean = {
      val first = p._1
      val second = p._2

      for (sp <- u.toList) {
        val v = sp._1
        val e = sp._2
        if (!e.isInstanceOf[Var]) {
          if (getSetOfVars(first) contains v) {
            //check if the second contains e
            if (e.occursIn(second) && (getSetOfVars(e) contains v)) {
              return false
            }
          } else if (getSetOfVars(second) contains v) {
            if (e.occursIn(first) && (getSetOfVars(e) contains v)) {
              return false
            }
          }
        }
      }

      true
    }

    def isUnifiable(p: (E, E))(implicit unifiableVariables: MSet[Var]) = unify(p :: Nil)(unifiableVariables) match {
      case None => false
      case Some(u) => {
        occurCheck(p, u) //originally returned 'true'
      }
    }
    def isUnifiableWrapper(p: (E, E)) = {
      val outa = isUnifiable(p)(unifiableVariables) // && 
      val outb = !(p._1.equals(p._2))
      outa && outb
    }

    val unifiablePairsC = (for (auxL <- seq.suc; auxR <- seq.suc) yield (auxL, auxR)).filter(isUnifiableWrapper)
    val unifiablePairsD = (for (auxL <- seq.ant; auxR <- seq.ant) yield (auxL, auxR)).filter(isUnifiableWrapper)
    val finalUnifiablePairsList = unifiablePairsC ++ unifiablePairsD
    if (finalUnifiablePairsList.length > 0) {
      val p = finalUnifiablePairsList.head

      val sub = unify(p :: Nil)(unifiableVariables) match {
        case None => throw new Exception("Contraction failed.")
        case Some(u) => {
          u
        }
      }

      val cleanSuc = (for (auxL <- seq.suc) yield sub(auxL))
      val cleanAnt = (for (auxL <- seq.ant) yield sub(auxL))

      val sA = addAntecedents(cleanAnt.distinct.toList)
      val sS = addSuccedents(cleanSuc.distinct.toList)
      val seqOut = sS union sA

      if (subs == null) {
        contract(seqOut, List[Substitution](sub))
      } else {
        contract(seqOut, subs ++ List[Substitution](sub))
      }
    } else {
      (seq.ant.distinct, seq.suc.distinct, subs)
    }
  }

}

object Contraction {
  def apply(premise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {
    new Contraction(premise, Sequent()())
  }
  def apply(premise: SequentProofNode, desired: Sequent)(implicit unifiableVariables: MSet[Var]) = {
    new Contraction(premise, desired)
  }

  def unapply(p: SequentProofNode) = p match {
    case p: Contraction => Some((p.premise, p.desired))
    case _ => None
  }
}
