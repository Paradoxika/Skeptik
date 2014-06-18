package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.{Axiom,R}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import collection.mutable.{Queue, HashMap => MMap}
import at.logic.skeptik.proof.Proof

/*
 * 
 * not yet modified; still just a copy of LowerUnits
 * 
 * 
 */

object FOLowerUnits 
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {
  // ToDo: optimize this by interlacing collectUnits and fixProofNodes
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
        case R(left,right,_,_) if unitsSet contains left => fixedRight
        case R(left,right,_,_) if unitsSet contains right => fixedLeft
        case R(left,right,pivot,_) => R(fixedLeft, fixedRight, pivot)
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
    val root = units.map(fixMap).foldLeft(fixMap(proof.root))((left,right) => try {R(left,right)} catch {case e:Exception => left})
    Proof(root)
  }

}
