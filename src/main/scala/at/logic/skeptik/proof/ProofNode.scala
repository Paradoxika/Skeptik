package at.logic.skeptik.proof

import annotation.tailrec
import collection.mutable.{HashSet => MSet, Stack}

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

    // As tail recursion is impossible, the fastest solution is to implement our own stack
    val todo = new Stack[P]()

    def pushPremises(node: P): Unit = 
      for (prem <- node.premises if !visited(prem)) {
        visited += prem
        todo.push(prem)
      }
    pushPremises(self)

    @tailrec def visit(): Boolean =
      if (todo.isEmpty)
        false
      else {
        val node = todo.pop
        if (predicate(node))
          true
        else {
          pushPremises(node)
          visit()
        }
      }
    visit()
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
