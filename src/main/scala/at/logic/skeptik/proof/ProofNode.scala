package at.logic.skeptik.proof

import annotation.tailrec
import collection.mutable.{HashSet => MSet}

import at.logic.skeptik.judgment.Judgment

abstract class ProofNode[+J <: Judgment, +P <: ProofNode[J,P]] 
{
  def name = {val fullName = getClass.getName; fullName.substring(fullName.lastIndexOf('.' : Int))}
  private val self = asInstanceOf[P]
  def premises: Seq[P]
  def conclusion : J
  def parameters: Seq[Any] = Nil

  def existsAmongAncestors(predicate: (P) => Boolean): Boolean = {
    val visited = MSet(self)

    def visit(node: P): Boolean = {
      if (visited contains node)
        false
      else
        visited += node
        predicate(node) || (node.premises exists visit)
    }

    premises exists visit
  }
}

trait GenNullary[+J <: Judgment, +P <: ProofNode[J,P]] extends ProofNode[J,P] { def premises = Seq() }

trait GenUnary[+J <: Judgment, +P <: ProofNode[J,P]] extends ProofNode[J,P] {
  def premise: P
  def premises = Seq(premise)
}

trait GenBinary[+J <: Judgment, +P <: ProofNode[J,P]] extends ProofNode[J,P] {
  def leftPremise: P
  def rightPremise: P
  def premises = Seq(leftPremise, rightPremise)
}
