package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk.{Axiom,CutIC}
import at.logic.skeptik.judgment.Sequent
import collection.mutable.{Queue, HashMap => MMap}
import at.logic.skeptik.proof.ProofNodeCollection

object NewUnitLowering extends Function1[SequentProof,SequentProof] {

  private def collectUnits(proofs: ProofNodeCollection[SequentProof]) = {
    def isUnitClause(s:Sequent) = s.ant.length + s.suc.length == 1
    proofs.foldRight(Nil:List[SequentProof])((node, acc) =>
      if (isUnitClause(node.conclusion) && proofs.childrenOf(node).length > 1) node::acc else acc
    );
  }

  private def fixProofs(unitsSet: Set[SequentProof], proofs: ProofNodeCollection[SequentProof]) = {
    val fixMap = MMap[SequentProof,SequentProof]()

    def visit (node: SequentProof, fixedPremises: List[SequentProof]) = {
      lazy val fixedLeft  = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;
      val fixedP = node match {
        case Axiom(conclusion) => Axiom(conclusion)
        case CutIC(left,right,_,_) if unitsSet contains left => fixedRight
        case CutIC(left,right,_,_) if unitsSet contains right => fixedLeft
        case CutIC(left,right,aux,_) => CutIC(fixedLeft, fixedRight, _ == aux)
      }
      if (node == proofs.root || unitsSet.contains(node)) fixMap.update(node, fixedP)
      fixedP
    }
    proofs.foldDown(visit)
    fixMap
  }

  def apply(proof: SequentProof) = {
    val proofs  = ProofNodeCollection(proof)
    val units   = collectUnits(proofs)
//    println(units.length + " units")
    val fixMap  = fixProofs(units.toSet, proofs)
    units.map(fixMap).foldLeft(fixMap(proof))((left,right) => try {CutIC(left,right)} catch {case e:Exception => left})
  }
}



