package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk.{Axiom,CutIC}
import at.logic.skeptik.judgment.Sequent
import collection.mutable.{Queue, HashMap => MMap}
import at.logic.skeptik.proof.ProofNodeCollection

object NewUnitLowering
extends CompressorAlgorithm[SequentProof] with IdempotentAlgorithm[SequentProof] {

  private def collectUnits(proof: ProofNodeCollection[SequentProof]) = {
    def isUnitClause(s:Sequent) = s.ant.length + s.suc.length == 1
    proof.foldRight(Nil:List[SequentProof])((node, acc) =>
      if (isUnitClause(node.conclusion) && proof.childrenOf(node).length > 1) node::acc else acc
    );
  }

  private def fixProofs(unitsSet: Set[SequentProof], proof: ProofNodeCollection[SequentProof]) = {
    val fixMap = MMap[SequentProof,SequentProof]()

    def visit (node: SequentProof, fixedPremises: List[SequentProof]) = {
      lazy val fixedLeft  = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;
      val fixedP = node match {
        case Axiom(conclusion) => node
        case CutIC(left,right,_,_) if unitsSet contains left => fixedRight
        case CutIC(left,right,_,_) if unitsSet contains right => fixedLeft
        case CutIC(left,right,aux,_) => CutIC(fixedLeft, fixedRight, _ == aux)
      }
      if (node == proof.root || unitsSet.contains(node)) fixMap.update(node, fixedP)
      fixedP
    }
    proof.foldDown(visit)
    fixMap
  }

  def apply(proof: ProofNodeCollection[SequentProof]) = {
    val units   = collectUnits(proof)
//    println(units.length + " units")
    val fixMap  = fixProofs(units.toSet, proof)
    val root = units.map(fixMap).foldLeft(fixMap(proof.root))((left,right) => try {CutIC(left,right)} catch {case e:Exception => left})
    ProofNodeCollection(root)
  }

}
