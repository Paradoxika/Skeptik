package at.logic.skeptik.judgment.immutable

import at.logic.skeptik.expression.{E, Var}
import at.logic.skeptik.judgment.{Sequent, SequentLike}

/**
  * Represents a fully propositional sequent (contains only Vars).
  *
  * @author Daniyar Itegulov
  */
class VarSeqSequent(val ant: Seq[Var], val suc: Seq[Var]) extends Sequent with SequentLike[VarSeqSequent] {
  lazy val literals: Seq[UnitSequent] =
    ant.map(UnitSequent(_, negated = true)) ++ suc.map(UnitSequent(_, negated = false))

  def apply(pos: Int): UnitSequent = literals(pos)

  def first: UnitSequent = apply(0)

  def last: UnitSequent = apply(literals.length - 1)

  def +(f: E) = f match {
    case v: Var => new VarSeqSequent(ant, suc :+ v)
    case _ => throw new UnsupportedOperationException
  }

  def +:(f: E) = f match {
    case v: Var => new VarSeqSequent(ant :+ v, suc)
    case _ => throw new UnsupportedOperationException
  }

  def -(f: E) = new VarSeqSequent(ant, suc.filterNot(_ == f))

  def -:(f: E) = new VarSeqSequent(ant.filterNot(_ == f), suc)

  def union(that: Sequent) = that match {
    case varSeq: VarSeqSequent => new VarSeqSequent(ant union varSeq.ant, suc union varSeq.suc)
    case _ => throw new UnsupportedOperationException
  }

  def diff(that: Sequent) = that match {
    case varSeq: VarSeqSequent => new VarSeqSequent(ant diff varSeq.ant, suc diff varSeq.suc)
    case _ => throw new UnsupportedOperationException
  }

  def intersect(that: Sequent) = that match {
    case varSeq: VarSeqSequent => new VarSeqSequent(ant intersect varSeq.ant, suc intersect varSeq.suc)
    case _ => throw new UnsupportedOperationException
  }
}

object VarSeqSequent {
  def apply(ant: Var*)(suc: Var*) = new VarSeqSequent(ant, suc)
}
