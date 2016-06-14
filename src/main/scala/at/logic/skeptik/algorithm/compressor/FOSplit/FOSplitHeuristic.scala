package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.algorithm.unifier.MartelliMontanari
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.{E, Var}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

/**
  * Created by eze on 2016.06.13..
  */
trait AbstractFOSplitHeuristic extends FOSplit {
  def computeMeasures(proof: Proof[Node]): (MMap[E,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long): E

  def selectLiteral(proof: Proof[Node]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    chooseVariable(measureMap, measureSum)
  }
}

trait SeenLiteralsHeuristic extends AbstractFOSplitHeuristic {
  def exploreLiterals(proof: Proof[Node]) : MMap[String,Option[E]] = {
    def getLiteralName(literal: E) : String = literal match {
      case Atom(Var(name,_),_) => name
      case _                   => throw new Exception("Literal name not found: " + literal.toString)
    }
    def unifyIfPossible(literal1 : Option[E] , literal2 : Option[E]) : Option[E] = {
      if(literal1.isEmpty || literal2.isEmpty)
        None
      else {
        val mgu = MartelliMontanari((literal1.get,literal2.get)::Nil)(this.variables)
        mgu match {
          case None       => None
          case Some(subs) => Some(subs(literal1.get))
        }
      }
    }
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

  def availableLiterals(literals : MMap[String,Option[(E,E)]]) : MSet[String] = {
    val available = literals.filter(_._2.nonEmpty)
    MSet(available.keys.toList: _*)
  }

  def computeMeasures(proof: Proof[Node]): (MMap[E,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long): E
}