package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.{Axiom,CutIC}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import collection.mutable.{Queue, HashMap => MMap}
import at.logic.skeptik.proof.Proof

object LowerUnits 
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {

  private def collectUnits(proof: Proof[SequentProofNode]) = {
    def isUnitClause(s:Sequent) = s.ant.length + s.suc.length == 1
    (proof :\ (Nil:List[SequentProofNode])) { (node, acc) =>
      if (isUnitClause(node.conclusion) && proof.childrenOf(node).length > 1) node::acc else acc
    }
  }

  private def fixProofNodes(unitsSet: Set[SequentProofNode], proof: Proof[SequentProofNode]) = {
    val fixMap = MMap[SequentProofNode,SequentProofNode]()

    def visit (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
      lazy val fixedLeft  = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;
      val fixedP = node match {
        case Axiom(conclusion) => node
        case CutIC(left,right,_,_) if unitsSet contains left => fixedRight
        case CutIC(left,right,_,_) if unitsSet contains right => fixedLeft
        case CutIC(left,right,aux,_) => CutIC(fixedLeft, fixedRight, _ == aux)
        case _ => node
      }
      if (node == proof.root || unitsSet.contains(node)) fixMap.update(node, fixedP)
      fixedP
    }
    proof.foldDown(visit)
    fixMap
  }

  def apply(proof: Proof[SequentProofNode]) = {
    val units   = collectUnits(proof)
    val fixMap  = fixProofNodes(units.toSet, proof)
    val root = units.map(fixMap).foldLeft(fixMap(proof.root))((left,right) => try {CutIC(left,right)} catch {case e:Exception => left})
    Proof(root)
  }

}
