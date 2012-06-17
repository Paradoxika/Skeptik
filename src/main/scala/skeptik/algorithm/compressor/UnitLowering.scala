package skeptik.algorithm.compressor

import skeptik.proof.sequent._
import skeptik.proof.sequent.lk.{Axiom,CutIC}
import skeptik.judgment.Sequent
import scala.collection.mutable.{Queue, HashMap => MMap}
import skeptik.proof.ProofNodeCollection

object NewUnitLowering extends Function1[SequentProof,SequentProof] {

  // made public for debug. TODO: private
  def collectUnits(proofs: ProofNodeCollection[SequentProof]) = {
    def isUnitClause(s:Sequent) = s.ant.length + s.suc.length == 1
    proofs.foldRight(Nil:List[SequentProof])((p, acc) =>
      if (isUnitClause(p.conclusion) && proofs.childrenOf(p).length > 1) p::acc else acc
    );
  }

  // made public for debug. TODO: private
  def fixProofs(unitsSet: Set[SequentProof], proofs: ProofNodeCollection[SequentProof]) = {
    val fixMap = MMap[SequentProof,SequentProof]()

    def visit (p: SequentProof, fixedPremises: List[SequentProof]) = {
      lazy val fixedLeft  = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;
      val fixedP = p match {
        case Axiom(conclusion) => Axiom(conclusion)
        case CutIC(left,right,_,_) if unitsSet contains left => fixedRight
        case CutIC(left,right,_,_) if unitsSet contains right => fixedLeft
        case CutIC(left,right,auxL,auxR) => CutIC(fixedLeft, fixedRight, auxL, auxR)
      }
      if (p == proofs.root || unitsSet.contains(p)) fixMap.update(p, fixedP)
      fixedP
    }
    proofs.foldDown(visit)
    fixMap
  }

  def apply(p: SequentProof) = {
    val proofs  = ProofNodeCollection(p)
    val units   = collectUnits(proofs)
    val fixMap  = fixProofs(units.toSet, proofs)
    units.map(fixMap).foldLeft(fixMap(p))((left,right) => try {CutIC(left,right)} catch {case e:Exception => left})
  }
}



