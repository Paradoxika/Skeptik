package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{Axiom,R}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Clause}
import collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.Proof

import scala.language.postfixOps

object LowerUnits extends (Proof[Node] => Proof[Node]) {
  
  private def collectUnits(proof: Proof[Node]) = {
    def isUnitClause(c:Clause) = c.ant.length + c.suc.length == 1
    
    proof filter { node => (isUnitClause(node.conclusion) && proof.childrenOf(node).length > 1)}
  }

  private def fixProof(units: Set[Node], proof: Proof[Node]) = {
    val fixed = MMap[Node,Node]()

    proof foldDown { (node: Node, fixedPremises: Seq[Node]) => 
      lazy val fixedLeft  = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;
      val fixedP = node match {
        case Axiom(conclusion) => node
        case R(left,right,_,_) if units contains left => fixedRight
        case R(left,right,_,_) if units contains right => fixedLeft
        case R(left,right,pivot,_) => R(fixedLeft, fixedRight, pivot)
        case _ => node
      }
      if (node == proof.root || (units contains node) ) fixed(node) = fixedP
      fixedP 
    }
    fixed
  }

  def apply(proof: Proof[Node]) = {
    val units   = collectUnits(proof)
    val fixed  = fixProof(units.toSet, proof)
    val root = (fixed(proof.root) /: (units map fixed)) {
      (left,right) => try {R(left,right)} catch {case e:Exception => left}
    }
    Proof(root)
  }
}
