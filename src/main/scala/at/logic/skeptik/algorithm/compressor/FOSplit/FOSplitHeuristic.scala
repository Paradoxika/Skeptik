package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.algorithm.unifier.MartelliMontanari
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.{App, E, Var}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

/**
  * Created by eze on 2016.06.13..
  */
trait AbstractFOSplitHeuristic extends FOSplit {
  def computeMeasures(proof: Proof[Node]): (MMap[String,Long],Long)

  def chooseVariable(literalAdditivity: collection.Map[String,Long], totalAdditivity: Long): Option[E]

  def selectLiteral(proof: Proof[Node]) = {
    val (measureMap, measureSum) = computeMeasures(proof)
    chooseVariable(measureMap, measureSum)
  }
}


trait SeenLiteralsHeuristic extends AbstractFOSplitHeuristic {

  private def getLiteralName(literal: E) : String =
    literal match {
        case Atom(Var(name,_),_) => name
        case App(function,arg)   => getLiteralName(function)
        case Var(name,_)         => name
        case _                   => throw new Exception("Literal name not found: " + literal.toString)
    }

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

  private def getLiteralName(literal: E) : String =
    literal match {
      case Atom(Var(name,_),_) => name
      case App(function,arg)   => getLiteralName(function)
      case Var(name,_)         => name
      case _                   => throw new Exception("Literal name not found: " + literal.toString)
    }

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