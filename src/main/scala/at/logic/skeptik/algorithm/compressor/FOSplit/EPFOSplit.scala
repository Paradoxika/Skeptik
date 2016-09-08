package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.algorithm.compressor.Timeout
import at.logic.skeptik.algorithm.unifier.MartelliMontanari
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.expression.term.FunctionTerm
import at.logic.skeptik.expression.{Abs, App, AppRec, E, Var, i}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

/**
  * In this version of FO Splitting we will not split over all occurrences of a literal.
  * Instead if we select one instance of a literal for splitting we will split over it and
  * all the alpha equivalent occurrences of it.
  */
class EPFOSplit(override val variables : collection.mutable.Set[Var], val timeout : Int)
extends FOSplit(variables) with EPFOAdditivityHeuristic with EPFOHighestAdditivityChoice with Timeout
with IndependentVariablesHeuristic with AlphaEquivalenceAsEquality {
}


trait AbstractEPFOSplitHeuristic extends FOSplit {
  protected def getLiteralName(literal: E) : String =
    literal match {
      case Atom(Var(name,_),_) => name
      case App(function,arg)   => getLiteralName(function)
      case Var(name,_)         => name
      case _                   => throw new Exception("Literal name not found: " + literal.toString)
    }

  def computeMeasures(proof: Proof[Node]): (MMap[E,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long): Option[E]

  def selectLiteral(proof: Proof[Node]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    chooseVariable(measureMap, measureSum)
  }
}

trait EPFOAdditivityHeuristic extends AbstractEPFOSplitHeuristic  {

  def computeMeasures(proof: Proof[Node]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[E,Long]()
    def visit(node: Node) = node match {
      case UnifyingResolution(_,_,leftResolveLiteral,rightResolveLiteral) =>
        val nodeAdditivity = ((node.conclusion.size - (node.premises.head.conclusion.size max node.premises(1).conclusion.size)) max 0) + 1
        totalAdditivity += nodeAdditivity
        literalAdditivity.update(leftResolveLiteral,literalAdditivity.getOrElse(leftResolveLiteral,0.toLong) + nodeAdditivity)
      case _ =>
    }
    proof.foreach(visit)
    (literalAdditivity, totalAdditivity)
  }
}



trait EPFOHighestAdditivityChoice extends AbstractEPFOSplitHeuristic {
  def chooseVariable(literalAdditivity: collection.Map[E, Long], totalAdditivity: Long) = {
    def maxAdd(literal1: (E, Long), literal2 : (E, Long)): (E, Long) =
      if (literal1._2 > literal2._2) literal1 else literal2
    val iterator = literalAdditivity.toIterator
    if (iterator.isEmpty) None
    else Some(iterator.reduceLeft(maxAdd)._1)
  }
}


trait IndependentVariablesHeuristic extends AbstractEPFOSplitHeuristic {

  def isIncludedInSet(sequent: Sequent, literalsSet : MSet[E]): Boolean = {
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


  def exploreLiterals(proof: Proof[Node]) : MMap[E,Option[E]] = {
    val literals = MMap[E, Option[E]]()
    val nodesSets = MMap[Node, MSet[E]]()

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
          if(node == leftPremise)
            literals += leftResolvedLiteral  -> None
          else
            literals += rightResolvedLiteral -> None
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





    def getVars(literal : E) : MSet[Var] =
      literal match {
        case Atom(_,terms)   => if(terms.isEmpty) MSet[Var]() else if(terms.size == 1) getVarsFromTerms(terms.head) else (terms map getVarsFromTerms) reduce (_ union _)
        case App(App(p,x),y) => getVars(App(p,x)) union getVarsFromTerms(y)
        case App(x,y)        =>
          require(x.t != i)
          getVarsFromTerms(y)
        case Var(_,_)        =>
          println("xcxzcz")
          MSet[Var]()
      }
    def getVarsFromTerms(term : E) : MSet[Var] = {
      term match {
        case FunctionTerm(_,args) => if(args.isEmpty) MSet[Var]() else if(args.size == 1) getVarsFromTerms(args.head) else (args map getVarsFromTerms) reduce (_ union _)
        case v @ Var(_,_)         => if(this.variables contains v) MSet[Var](v) else MSet[Var]()
        case AppRec(_,args)       => if(args.isEmpty) MSet[Var]() else if(args.size == 1) getVarsFromTerms(args.head) else (args map getVarsFromTerms) reduce (_ union _)
        case App(App(f,x),y)      => getVarsFromTerms(App(f,x)) union getVars(y)
        case App(f,y)             => getVarsFromTerms(y)
      }
    }

    def shareVariables(lit : E, premise : Node) : Boolean = {
      val premiseWithoutLit = (lit -: premise.conclusion) - lit
      val litVars = getVars(lit)
      val premiseLiteralsVars = (premiseWithoutLit.ant ++ premiseWithoutLit.suc) map getVars
      val premiseWithoutLitVars = if(premiseLiteralsVars.isEmpty) MSet[Var]() else if(premiseLiteralsVars.size == 1) premiseLiteralsVars.head else  premiseLiteralsVars reduce (_ union _)
      (litVars intersect premiseWithoutLitVars).nonEmpty
    }

    def update(lit : E, premise : Node) : Unit =
      if((literals contains lit)
        && shareVariables(lit,premise))
        literals += lit -> None
      else if((literals contains lit)
        && ! shareVariables(lit,premise))
        ()
      else if(shareVariables(lit,premise))
        literals += lit -> None
      else literals += lit -> Some(lit)

    proof bottomUp { (node: Node, resultFromParents : Seq[Node]) =>
      node match {
        case UnifyingResolution(leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral) =>
          update(leftResolvedLiteral,leftPremise)
          update(rightResolvedLiteral,rightPremise)
          checkInclusion(node,resultFromParents)
        case Axiom(sequent) =>
          sequent.ant.foreach(x => update(x,node))
          sequent.suc.foreach(x => update(x,node))
          checkInclusion(node,resultFromParents)
        case _ => checkInclusion(node,resultFromParents)
      }
    }
    literals
  }

  def availableLiterals(literals : MMap[E,Option[E]]) : MSet[E] = {
    val available = literals.filter(_._2.nonEmpty)
    MSet(available.keys.toList: _*)
  }

  def computeMeasures(proof: Proof[Node]): (MMap[E,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long): Option[E]

  override def selectLiteral(proof: Proof[Node]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    val literals : MSet[E] = availableLiterals(exploreLiterals(proof))
    val availableLiteralsMap = measureMap.filter(x => literals.contains(x._1))
    chooseVariable(availableLiteralsMap, measureSum)
  }
}
