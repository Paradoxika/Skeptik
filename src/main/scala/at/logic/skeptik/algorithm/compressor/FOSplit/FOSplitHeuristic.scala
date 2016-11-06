package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.algorithm.unifier.MartelliMontanari
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.expression.{Abs, App, E, Var, i}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

object TestInclusion {

  protected def getLiteralName(literal: E) : String =
    literal match {
      case Atom(Var(name,_),_) => name
      case App(function,arg)   => getLiteralName(function)
      case Var(name,_)         => name
      case _                   => throw new Exception("Literal name not found: " + literal.toString)
    }

  def isIncludedInSet(sequent: Sequent, literalsSet : MSet[E], variables : collection.mutable.Set[Var]): Boolean = {

    val literals = sequent.ant ++ sequent.suc

    if(literals.isEmpty && literalsSet.isEmpty) return true

    val constantPrefix = "converted_to_constant_"

    def convertVariablesIntoNewConstants(e: E): E =
      e match {
        case Var(name, typ) => if (Character.isUpperCase(name.charAt(0))) Var(constantPrefix + name, typ) else Var(name, typ)
        case App(fun, arg) => App(convertVariablesIntoNewConstants(fun), convertVariablesIntoNewConstants(arg))
        case Abs(x, body) => Abs(convertVariablesIntoNewConstants(x).asInstanceOf[Var], convertVariablesIntoNewConstants(body))
      }

    // We first convert all variables in the literals set to constants so we can calculate substitutions
    // that only act on the literals that come from the sequent
    val literalSetWithoutVariables = literalsSet.map(convertVariablesIntoNewConstants)

    // Now, for each literal we calculate the occurrences of a literal with the same name in the set
    // Note that a literal like q(X) may have more than one occurrence in the set, e.g. q(a),q(converted_to_constant_X)
    val occurrences: MMap[E, List[E]] = MMap[E, List[E]]()
    for (l <- literals)
      occurrences += (l -> literalSetWithoutVariables.filter(getLiteralName(_) == getLiteralName(l)).toList)

    val literalSubstitutions: MMap[E, List[Substitution]] =
      occurrences map {
        case (e1, ls) =>
          e1 -> ls.map(x => MartelliMontanari((e1, x) :: Nil)(variables)).filter(_.nonEmpty).map(_.get)
      }

    // If we find a literal that can't be included in the
    // set we know that the whole set won't be contained
    for (l <- literals)
      if (literalSubstitutions(l).isEmpty) return false

    def createCompatibleSubstitution(restriction : MMap[Var,E],subs: List[List[Substitution]]): List[Substitution] =
      subs match {
        case Nil      => List(Substitution(restriction.toList :_*))
        case x :: xs  =>
          x flatMap { s =>
            val newRestrictions = restriction.clone()
            val pairs           = s.iterator
            var satissfyRestrictions = true
            for((v,e) <- pairs) {
              if (!(newRestrictions contains v))
                newRestrictions += (v -> e)
              else if (newRestrictions(v) != e)
                satissfyRestrictions = false
            }
            if(satissfyRestrictions) createCompatibleSubstitution(newRestrictions,xs)
            else Nil
          }
      }


    val substitutionByLiteralName = MMap[String,List[Substitution]]()
    val literalsNames = literalSubstitutions.keySet.map(getLiteralName)
    for(l <- literalsNames) {
      val substitutionsToCompare = literalSubstitutions.filter({case (k, v) => getLiteralName(k) == l}).values.toList
      substitutionByLiteralName += (l -> createCompatibleSubstitution(MMap[Var,E](),substitutionsToCompare))
    }

    // And we repeat the process with the substitutions of each literalName
    val substitutions = createCompatibleSubstitution(MMap[Var,E](),substitutionByLiteralName.values.toList)
    if(substitutions.isEmpty)
      false
    else {
      val randomSub = substitutions.head // Any substitution of the list should be fine
      (literals map {x => randomSub(x)}).toSet subsetOf literalSetWithoutVariables
    }
  }

  def main(args: Array[String]) = {
    val testSeq = Sequent()(List(Atom("p3", List(Var("U", i), Var("W", i))), Atom("p3", List(Var("U", i), Var("V", i))), Atom("p3", List(Var("W", i), Var("V", i)))): _*)
    val testSet = MSet(Atom("p3", List(Var("V", i), Var("V", i))), Atom("p3", List(Var("c21", i), Var("c19", i))), Atom("p3", List(Var("c19", i), Var("c21", i))))
    val s = Sequent(Atom("q",List(Var("V136",i))))(Atom("p",List(Var("a",i))))
    val set = MSet(Atom("q",List(Var("Z",i))),Atom("p",List(Var("a",i))))
    println(isIncludedInSet(s, set,MSet(Var("V136",i),Var("Z",i))))
  }
}

/**
  * The trait AbstractFOSplitHeuristic is the base trait of the ones
  * that should implement some abstract methods FOSplit.
  */
trait AbstractFOSplitHeuristic extends FOSplit {

  protected def getLiteralName(literal: E) : String =
    literal match {
      case Atom(Var(name,_),_) => name
      case App(function,arg)   => getLiteralName(function)
      case Var(name,_)         => name
      case _                   => throw new Exception("Literal name not found: " + literal.toString)
    }

  def computeMeasures(proof: Proof[Node]): (MMap[String,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[String,Long], totalAdditivity: Long): Option[E]

  def selectLiteral(proof: Proof[Node]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    chooseVariable(measureMap, measureSum)
  }
}


/**
  * The trait SeenLiteralsHeuristic explores the proof and checks for each literal if all the its uses
  * in resolution steps are unifiable. The hope is that the literals that satisfy this condition can be
  * consider for splitting. Unfortunatelly, experiments showed that some cases that satisfy this condition
  * fail to generate two proofs that can be resolved after splitting.
  *
  */
trait SeenLiteralsHeuristic extends AbstractFOSplitHeuristic {

  private def unifyIfPossible(literal1 : Option[E] , literal2 : Option[E]) : Option[E] =
    if(literal1.isEmpty || literal2.isEmpty)
      None
    else {
      val mgu = MartelliMontanari((literal1.get,literal2.get)::Nil)(this.variables)
      mgu match {
        case None       => None
        case Some(subs) => Some(subs(literal1.get))
      }
    }

  /**
    * The method exploreLiterals is the one that explores the proof
    * to check for each literal if all its uses as pivot are unifiable
    * along the proof
    *
    * @param proof The proof to explore
    * @return      A map from the literal name to the most restricted
    *              unification found. None is used if not all uses are
    *              unifiable. If they are, then the unified literal is
    *              stored in the map.
    */
  def exploreLiterals(proof: Proof[Node]) : MMap[String,Option[E]] = {
    val literals = MMap[String, Option[E]]()
    proof foldDown { (node: Node, _: Seq[Unit]) =>
      node match {
        case Axiom(_)          => ()
        case Contraction(_, _) => ()
        case UnifyingResolution(_, _, leftResolvedLiteral, rightResolvedLiteral) =>
          val literalName = getLiteralName(leftResolvedLiteral)
          val mgu         = MartelliMontanari((leftResolvedLiteral, rightResolvedLiteral) :: Nil)(this.variables) match {
            case Some(s) => s
            case None    => throw new Exception("Resolved Literals can't be unified: " + leftResolvedLiteral.toString + ", " + rightResolvedLiteral.toString)
          }
          val unifiedLiteral = mgu(leftResolvedLiteral)
          if(literals.contains(literalName)) {
            val oldLiteral = literals.get(literalName).get
            val newLiteral = unifyIfPossible(oldLiteral,Some(unifiedLiteral))
            literals += (literalName -> newLiteral)
          }
          else
            literals += (literalName -> Some(unifiedLiteral))
          ()
      }
    }
    literals
  }

  def availableLiterals(literals : MMap[String,Option[E]]) : MSet[String] = {
    val available = literals.filter(_._2.nonEmpty)
    MSet(available.keys.toList: _*)
  }

  def computeMeasures(proof: Proof[Node]): (MMap[String,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[String,Long], totalAdditivity: Long): Option[E]

  override def selectLiteral(proof: Proof[Node]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    val literals : MSet[String] = availableLiterals(exploreLiterals(proof))
    val availableLiteralsMap = measureMap.filter(x => literals.contains(x._1))
    chooseVariable(availableLiteralsMap, measureSum)
  }
}

trait FOAdditivityHeuristic extends AbstractFOSplitHeuristic  {

  def computeMeasures(proof: Proof[Node]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[String,Long]()
    def visit(node: Node) = node match {
      case UnifyingResolution(_,_,leftResolveLiteral,rightResolveLiteral) =>
        val nodeAdditivity = ((node.conclusion.size - (node.premises.head.conclusion.size max node.premises(1).conclusion.size)) max 0) + 1
        totalAdditivity += nodeAdditivity
        val literalName = getLiteralName(leftResolveLiteral)
        literalAdditivity.update(literalName,literalAdditivity.getOrElse(literalName,0.toLong) + nodeAdditivity)
      case _ =>
    }
    proof.foreach(visit)
    (literalAdditivity, totalAdditivity)
  }
}


/**
  * In this heuristic we experiment with a restriction similar to the
  * one implied in FORPI related to safe literals. Here we consider all
  * the literals resolved.
  */
trait SetContentionHeuristic extends AbstractFOSplitHeuristic {

  protected def isIncludedInSet(sequent: Sequent, literalsSet : MSet[E]): Boolean = {
    val constantPrefix = "converted_to_constant_"
    def convertVariablesIntoNewConstants(e: E): E =
      e match {
        case Var(name, typ) => if (Character.isUpperCase(name.charAt(0))) Var(constantPrefix + name, typ) else Var(name, typ)
        case App(fun, arg) => App(convertVariablesIntoNewConstants(fun), convertVariablesIntoNewConstants(arg))
        case Abs(x, body) => Abs(convertVariablesIntoNewConstants(x).asInstanceOf[Var], convertVariablesIntoNewConstants(body))
      }

    def createCompatibleSubstitution(restriction : MMap[Var,E],subs: List[List[Substitution]]): List[Substitution] =
      subs match {
        case Nil      => List(Substitution(restriction.toList :_*))
        case x :: xs  =>
          x flatMap { s =>
            val newRestrictions = restriction.clone()
            val pairs           = s.iterator
            var satissfyRestrictions = true
            for((v,e) <- pairs) {
              if (!(newRestrictions contains v))
                newRestrictions += (v -> e)
              else if (newRestrictions(v) != e)
                satissfyRestrictions = false
            }
            if(satissfyRestrictions) createCompatibleSubstitution(newRestrictions,xs)
            else Nil
          }
      }


    val literals = sequent.ant ++ sequent.suc

    if(literals.isEmpty && literalsSet.isEmpty) return true

    // We first convert all variables in the literals set to constants so we can calculate substitutions
    // that only act on the literals that come from the sequent
    val literalSetWithoutVariables = literalsSet.map(convertVariablesIntoNewConstants)

    // Now, for each literal we calculate the occurrences of a literal with the same name in the set
    // Note that a literal like q(X) may have more than one occurrence in the set, e.g. q(a),q(converted_to_constant_X)
    val occurrences: MMap[E, List[E]] = MMap[E, List[E]]()
    for (l <- literals)
      occurrences += (l -> literalSetWithoutVariables.filter(getLiteralName(_) == getLiteralName(l)).toList)

    val literalSubstitutions: MMap[E, List[Substitution]] =
      occurrences map {
        case (e1, ls) =>
          e1 -> ls.map(x => MartelliMontanari((e1, x) :: Nil)(this.variables)).filter(_.nonEmpty).map(_.get)
      }

    // If we find a literal that can't be included in the
    // set we know that the whole set won't be contained
    for (l <- literals)
      if (literalSubstitutions(l).isEmpty) return false

    val substitutionByLiteralName = MMap[String,List[Substitution]]()
    val literalsNames = literalSubstitutions.keySet.map(getLiteralName)
    for(l <- literalsNames) {
      val substitutionsToCompare = literalSubstitutions.filter({case (k, v) => getLiteralName(k) == l}).values.toList
      substitutionByLiteralName += (l -> createCompatibleSubstitution(MMap[Var,E](),substitutionsToCompare))
    }

    // And we repeat the process with the substitutions of each literalName
    val substitutions = createCompatibleSubstitution(MMap[Var,E](),substitutionByLiteralName.values.toList)
    if(substitutions.isEmpty)
      false
    else {
      val randomSub = substitutions.head // Any substitution of the list should be fine
      (literals map {x => randomSub(x)}).toSet subsetOf literalSetWithoutVariables
    }
  }


  def exploreLiterals(proof: Proof[Node]) : MMap[String,Option[E]] = {
    val nodesSets = MMap[Node, MSet[E]]()
    val literals  = MMap[String, Option[E]]()

    nodesSets +=  proof.root -> MSet[E](proof.root.conclusion.ant ++ proof.root.conclusion.suc :_* )

    proof bottomUp { (node: Node, resultFromParents : Seq[MSet[E]]) =>
      node match {
        case Axiom(_) => MSet[E]()
        case Contraction(premise, _) => nodesSets += premise -> nodesSets(node).clone() ; nodesSets(node).clone()
        case UnifyingResolution(leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral) =>
          val literalName = getLiteralName(leftResolvedLiteral)
          val mgu         = MartelliMontanari((leftResolvedLiteral, rightResolvedLiteral) :: Nil)(this.variables) match {
            case Some(s) => s
            case None    => throw new Exception("Resolved Literals can't be unified: " + leftResolvedLiteral.toString + ", " + rightResolvedLiteral.toString)
          }
          val unifiedLiteral : E = mgu(leftResolvedLiteral)
          literals  += literalName  -> Some(unifiedLiteral)
          val leftSet = if(resultFromParents.isEmpty) MSet[E]() else resultFromParents.reduceLeft(_ intersect _)
          nodesSets += leftPremise  -> (leftSet += unifiedLiteral) //(nodesSets(node).clone() += unifiedLiteral)
          nodesSets += rightPremise -> nodesSets(leftPremise)

          val leftSeq = Sequent()(leftPremise.conclusion.ant ++ leftPremise.conclusion.suc :_*)
          if(!isIncludedInSet(leftSeq,nodesSets(leftPremise)))
            literals += literalName -> None

          val rightSeq = Sequent()(rightPremise.conclusion.ant ++ leftPremise.conclusion.suc :_*)
          if(!isIncludedInSet(rightSeq,nodesSets(rightPremise)))
            literals += literalName -> None

          nodesSets(node).clone()
      }
    }
    literals
  }

  def availableLiterals(literals : MMap[String,Option[E]]) : MSet[String] = {
    val available = literals.filter(_._2.nonEmpty)
    MSet(available.keys.toList: _*)
  }

  def computeMeasures(proof: Proof[Node]): (MMap[String,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[String,Long], totalAdditivity: Long): Option[E]

  override def selectLiteral(proof: Proof[Node]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    val literals : MSet[String] = availableLiterals(exploreLiterals(proof))
    val availableLiteralsMap = measureMap.filter(x => literals.contains(x._1))
    chooseVariable(availableLiteralsMap, measureSum)
  }
}


//#####################################################
//#####################################################
//#####################################################

/**
  * This trait combines the SetContentionHeuristic and the SeenLiteralsHeuristic
  * in the hope of identifying more nodes that should not be used for splitting.
  *
  */
trait SetContentionAndSeenLiteralsHeuristic extends SetContentionHeuristic {

  private def unifyIfPossible(literal1 : Option[E] , literal2 : Option[E]) : Option[E] =
    if(literal1.isEmpty || literal2.isEmpty)
      None
    else {
      val mgu = MartelliMontanari((literal1.get,literal2.get)::Nil)(this.variables)
      mgu match {
        case None       => None
        case Some(subs) => Some(subs(literal1.get))
      }
    }


  override def exploreLiterals(proof: Proof[Node]) : MMap[String,Option[E]] = {
    val nodesSets = MMap[Node, MSet[E]]()
    val literals  = MMap[String, Option[E]]()

    nodesSets +=  proof.root -> MSet[E](proof.root.conclusion.ant ++ proof.root.conclusion.suc :_* )

    def intersectionOfParentsSets(node : Node, parents : Seq[Node]) : MSet[E] = {
      parents match {
        case Nil =>
          require(node == proof.root)
          MSet[E]().clone()
        case (n @ Contraction(premise,_)) :: Nil =>
          require(node == premise)
          nodesSets(n).clone()
        case (n @ UnifyingResolution(leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral)) :: Nil =>
          require(node == leftPremise || node == rightPremise)
          val mgu         = MartelliMontanari((leftResolvedLiteral, rightResolvedLiteral) :: Nil)(this.variables) match {
            case Some(s) => s
            case None    => throw new Exception("Resolved Literals can't be unified: " + leftResolvedLiteral.toString + ", " + rightResolvedLiteral.toString)
          }
          val unifiedLiteral : E = mgu(leftResolvedLiteral)
          nodesSets(n).clone() += unifiedLiteral
        case (n @ Contraction(premise,_)) :: ns  =>
          require(node == premise)
          nodesSets(n).clone() intersect intersectionOfParentsSets(node,ns)
        case (n @ UnifyingResolution(leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral)) :: ns =>
          require(node == leftPremise || node == rightPremise)
          val mgu         = MartelliMontanari((leftResolvedLiteral, rightResolvedLiteral) :: Nil)(this.variables) match {
            case Some(s) => s
            case None    => throw new Exception("Resolved Literals can't be unified: " + leftResolvedLiteral.toString + ", " + rightResolvedLiteral.toString)
          }
          val unifiedLiteral : E = mgu(leftResolvedLiteral)
          (nodesSets(n).clone() intersect intersectionOfParentsSets(node,ns)) += unifiedLiteral
      }
    }

    def removeLiteralsResolvedWithNode(node : Node, parents : Seq[Node]): Unit = {
      parents match {
        case Nil =>
        case UnifyingResolution(leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral) :: ns =>
          require(node == leftPremise || node == rightPremise)
          val literalName = getLiteralName(leftResolvedLiteral)
          literals += literalName -> None
          removeLiteralsResolvedWithNode(node,ns)
        case _ :: ns =>
          removeLiteralsResolvedWithNode(node,ns)
      }
    }

    def checkInclusion(node : Node, parents : Seq[Node]) : Node = {
      nodesSets += node -> intersectionOfParentsSets(node,parents)
      val nodeSeq = Sequent()(node.conclusion.ant ++ node.conclusion.suc :_*)
      if(!isIncludedInSet(nodeSeq,nodesSets(node)))
        removeLiteralsResolvedWithNode(node, parents)
      node
    }

    def checkResolvedLiteralIsUnifiable(leftResolvedLiteral : E, rightResolvedLiteral : E) : Unit = {
      val literalName = getLiteralName(leftResolvedLiteral)
      val mgu         = MartelliMontanari((leftResolvedLiteral, rightResolvedLiteral) :: Nil)(this.variables) match {
        case Some(s) => s
        case None    => throw new Exception("Resolved Literals can't be unified: " + leftResolvedLiteral.toString + ", " + rightResolvedLiteral.toString)
      }
      val unifiedLiteral : E = mgu(leftResolvedLiteral)
      if(literals.contains(literalName)) {
        val oldLiteral = literals.get(literalName).get
        val newLiteral = unifyIfPossible(oldLiteral,Some(unifiedLiteral))
        literals += (literalName -> newLiteral)
      }
      else
        literals += (literalName -> Some(unifiedLiteral))
    }

    /**
      * The method checkLiteralRepetition check the condition that the literal name is not used more than
      * once in each premise with the same sign (negated or without negation)
      *
      * @param leftPremise Left premise of the node being checked
      * @param rightPremise Right premise of the node being checked
      * @param literalName  The name of the literal to be checked
      */
    def checkLiteralRepetition(leftPremise : Node, rightPremise : Node, literalName : String) : Unit = {
      def numberOfOccurrences(premise : Node) : Int = {
        var occursNeg = 0
        var occursPos = 0
        for(e <- premise.conclusion.ant)
          if (getLiteralName(e) == literalName)
            occursNeg += 1
        for(e <- premise.conclusion.suc)
          if(getLiteralName(e) == literalName)
            occursPos += 1
        Math.max(occursNeg,occursPos)
      }

      if(numberOfOccurrences(leftPremise) > 1 || numberOfOccurrences(rightPremise) > 1)
        literals += (literalName -> None)
    }


    proof bottomUp { (node: Node, resultFromParents : Seq[Node]) =>
      node match {
        case Axiom(_) => checkInclusion(node,resultFromParents)
        case Contraction(premise, _) => checkInclusion(node,resultFromParents)
        case UnifyingResolution(leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral) =>
          checkLiteralRepetition(leftPremise, rightPremise, getLiteralName(leftResolvedLiteral))
          checkResolvedLiteralIsUnifiable(leftResolvedLiteral, rightResolvedLiteral)
          checkInclusion(node,resultFromParents)
      }
    }
    literals
  }

  override def availableLiterals(literals : MMap[String,Option[E]]) : MSet[String] = {
    val available = literals.filter(_._2.nonEmpty)
    MSet(available.keys.toList: _*)
  }

  def computeMeasures(proof: Proof[Node]): (MMap[String,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[String,Long], totalAdditivity: Long): Option[E]

  override def selectLiteral(proof: Proof[Node]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    val literals : MSet[String]  = availableLiterals(exploreLiterals(proof))
    val availableLiteralsMap     = measureMap.filter(x => literals.contains(x._1))
    chooseVariable(availableLiteralsMap, measureSum)
  }
}