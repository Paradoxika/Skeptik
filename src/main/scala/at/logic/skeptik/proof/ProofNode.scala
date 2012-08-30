package at.logic.skeptik.proof

import at.logic.skeptik.judgment.Judgment

abstract class ProofNode[+J <: Judgment, +P <: ProofNode[J,P]] 
{
  def name = {val fullName = getClass.getName; fullName.substring(fullName.lastIndexOf('.' : Int))}
  private val self = asInstanceOf[P]
  def premises: Seq[P]
  def conclusion : J
  def parameters: Seq[Any] = Nil
  
  @deprecated //ToDo: this method should be implemented in Proof instead. It is node the responsibility of a node to know everything above it.
  override def toString = {
    var counter = 0; var result = "";
    def visitNode(n:P, r:Seq[Int]): Int = {
      counter += 1
      result += counter.toString + ": {" + n.conclusion + "} \t:" +
                n.name + "(" + r.mkString(", ") + ")[" + parameters.mkString(", ") + "]\n"
      counter
    }
    Proof(self).foldDown(visitNode)
    result
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
