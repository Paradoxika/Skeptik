package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.algorithm.unifier.MartelliMontanari
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.expression.{App, E, Var}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

/**
  * Created by eze on 2016.06.13..
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
    * The method exploreLiterals, explores the proof to check if all
    * the uses of a literal as pivot are unifiable along the proof
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
        case UnifyingResolution(_, _, leftResolvedLiteral, rightResolvedLiteral) => {
          val literalName = getLiteralName(leftResolvedLiteral)
          val mgu         = MartelliMontanari((leftResolvedLiteral, rightResolvedLiteral) :: Nil)(this.variables) match {
            case Some(s) => s
            case None    => throw new Exception("Resolved Literasl can't be unified: " + leftResolvedLiteral.toString + ", " + rightResolvedLiteral.toString)
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

  // TODO: DEBUG THIS
  protected def isIncludeInSet(sequent: Sequent,literalsSet : MSet[E]): Boolean = {

    import UnifyingResolution._

    def desiredIsContained(computed: Sequent, desired: Sequent)(implicit unifiableVariables: MSet[Var]): Boolean = {
      if (computed == desired) {
        true
      } else {
        val commonVars = (getSetOfVars(Axiom(computed.ant)) intersect getSetOfVars(Axiom(computed.suc)))

        val antMap = generateSubstitutionOptions(computed.ant, desired.ant, unifiableVariables)
        if (getSetOfVars(desired.ant: _*).size > 0 && antMap.size == 0) {
          return false
        }
        val sucMap = generateSubstitutionOptions(computed.suc, desired.suc, unifiableVariables)
        if (getSetOfVars(desired.suc: _*).size > 0 && sucMap.size == 0) {
          return false
        }
        val intersectedMap = intersectMaps(antMap, sucMap)

        if (!validMap(intersectedMap, vars)) {
          return false
        }

        def findFromMap(m: MMap[Var, Set[E]], vars: MSet[Var]): Boolean = {
          val subList = MSet[(Var, E)]()

          for (k <- m.keySet) {
            if (m.get(k).get.size > 0) {
              subList.add((k, m.get(k).get.head))
            }
          }

          val sub = Substitution(subList.toSeq: _*)
          def foundExactly(target: Seq[E], source: Seq[E]): Boolean = {
            if (target.size == 0) {
              return true
            }
            target match {
              case h :: t => {
                for (s <- source) {
                  if (h.equals(s)) {
                    return foundExactly(t, source)
                  }
                }
              }
            }

            false
          }

          val newDesiredAnt = (desired.ant).map(e => sub(e))

          val newDesiredSuc = (desired.suc).map(e => sub(e))
          foundExactly(newDesiredAnt, computed.ant) && foundExactly(newDesiredSuc, computed.suc)
        }

        if (!findFromMap(intersectedMap, vars)) {
          return false
        }

        true
      }
    }

    def antVars = getSetOfVars(sequent.ant: _*)
    def sucVars = getSetOfVars(sequent.suc: _*)
    def antVarsB = getSetOfVars(literalsSet.toList:_*)//safeLit.ant: _*)
    def sucVarsB = getSetOfVars(literalsSet.toList:_*)//safeLit.suc: _*)
    def vars = MSet[Var]() ++ antVars ++ sucVars
    def allvars = MSet[Var]() ++ antVars ++ sucVars ++ antVarsB ++ sucVarsB

    def safeClean = fixSharedNoFilter(Axiom(literalsSet/*safeLit*/), Axiom(sequent), 0, allvars)

    desiredIsContained(safeClean.conclusion, sequent)(vars)
  }

  def exploreLiterals(proof: Proof[Node]) : MMap[String,Option[E]] = {
    val nodesSets = MMap[Node, MSet[E]]()
    val literals  = MMap[String, Option[E]]()

    nodesSets +=  proof.root -> MSet[E](proof.root.conclusion.ant ++ proof.root.conclusion.suc :_* )

    proof bottomUp { (node: Node, _ : Seq[Unit]) =>
      node match {
        case Axiom(_) => ()
        case Contraction(premise, _) => nodesSets += premise -> nodesSets(node).clone() ; ()
        case UnifyingResolution(leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral) => {
          val literalName = getLiteralName(leftResolvedLiteral)
          val mgu         = MartelliMontanari((leftResolvedLiteral, rightResolvedLiteral) :: Nil)(this.variables) match {
            case Some(s) => s
            case None    => throw new Exception("Resolved Literals can't be unified: " + leftResolvedLiteral.toString + ", " + rightResolvedLiteral.toString)
          }
          val unifiedLiteral : E = mgu(leftResolvedLiteral)
          literals += literalName -> Some(unifiedLiteral)
          nodesSets += leftPremise  -> (nodesSets(node).clone() += unifiedLiteral)
          nodesSets += rightPremise -> nodesSets(leftPremise)
          val leftSeq = Sequent()(leftPremise.conclusion.ant ++ leftPremise.conclusion.suc :_*)
          if(!isIncludeInSet(leftSeq,nodesSets(leftPremise))) {
            literals += literalName -> None
            println("Variables: " + variables.mkString(","))
            println("Left NOT included:\nPremise: " + leftPremise.conclusion.toString +"\nSet: " + nodesSets(leftPremise).mkString(","))
          }
          val rightSeq = Sequent()(rightPremise.conclusion.ant ++ leftPremise.conclusion.suc :_*)
          if(!isIncludeInSet(rightSeq,nodesSets(rightPremise))) {
            println("Variables: " + variables.mkString(","))
            literals += literalName -> None
            println("Right NOT included:\nPremise: " + rightPremise.conclusion.toString +"\nSet: " + nodesSets(rightPremise).mkString(","))
          }
          ()
        }
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
  * EXPERIMENT
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

    proof bottomUp { (node: Node, _ : Seq[Unit]) =>
      node match {
        case Axiom(_) => ()
        case Contraction(premise, _) => nodesSets += premise -> nodesSets(node) ; ()
        case UnifyingResolution(leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral) => {
          val literalName = getLiteralName(leftResolvedLiteral)
          val mgu         = MartelliMontanari((leftResolvedLiteral, rightResolvedLiteral) :: Nil)(this.variables) match {
            case Some(s) => s
            case None    => throw new Exception("Resolved Literasl can't be unified: " + leftResolvedLiteral.toString + ", " + rightResolvedLiteral.toString)
          }
          val unifiedLiteral : E = mgu(leftResolvedLiteral)
          if(literals.contains(literalName)) {
            val oldLiteral = literals.get(literalName).get
            val newLiteral = unifyIfPossible(oldLiteral,Some(unifiedLiteral))
            literals += (literalName -> newLiteral)
          }
          else
            literals += (literalName -> Some(unifiedLiteral))

          nodesSets += leftPremise  -> (nodesSets(node) += unifiedLiteral)
          nodesSets += rightPremise -> nodesSets(leftPremise)
          val leftSeq = Sequent()(leftPremise.conclusion.ant ++ leftPremise.conclusion.suc :_*)
          if(!isIncludeInSet(leftSeq,nodesSets(leftPremise))) {
            literals += literalName -> None
            println("Left NOT included:\nPremise: " + leftPremise.conclusion.toString +"\nSet: " + nodesSets(leftPremise).mkString(","))
          }
          val rightSeq = Sequent()(rightPremise.conclusion.ant ++ leftPremise.conclusion.suc :_*)
          if(!isIncludeInSet(rightSeq,nodesSets(rightPremise))) {
            literals += literalName -> None
            println("Right NOT included:\nPremise: " + rightPremise.conclusion.toString +"\nSet: " + nodesSets(rightPremise).mkString(","))
          }
          ()
        }
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
    val literals : MSet[String] = availableLiterals(exploreLiterals(proof))
    val availableLiteralsMap = measureMap.filter(x => literals.contains(x._1))
    chooseVariable(availableLiteralsMap, measureSum)
  }
}