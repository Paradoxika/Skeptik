package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.compressor.congruence._
import at.logic.skeptik.algorithm.compressor.split._
import at.logic.skeptik.algorithm.compressor.subsumption._
import at.logic.skeptik.algorithm.compressor.reduceAndReconstruct._
import at.logic.skeptik.algorithm.compressor.pebbler._
import at.logic.skeptik.expression.E
import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.proof.sequent.lk.R

// Algorithm names should contain only alphanumeric characters

// ToDo: the name of an algorithm should be a property defined in the algorithm's class

package object compressor {
  val paramAlgorithms = Map(
      "LastChildDecay" -> LastChildOfDecayPebbler
  )
  
  
  val algorithms = Map(
    "D" -> DAGify,
    "ET" -> EliminateTautologies,
    "RU" -> RecycleUnits,
    "TDRU" -> TopDownRecycleUnits,
    "RP" -> RecyclePivots,
    "RPI" -> RecyclePivotsWithIntersection,
    "RPC" -> RecyclePivotsWithConclusionSequent,
    "LU" -> LowerUnits,
    "LUV" -> LowerUnivalents,
    "RPI3LU" -> IdempotentThreePassLowerUnits,
    "LUVRPI" -> IdempotentLowerUnivalentsAfterRecyclePivots,
    "RPI3LUV" -> LowerUnivalentsBeforeRecyclePivots,
    
    "RR" -> new ReduceAndReconstructS1P(5000),
    "RRM" -> new ReduceAndReconstructMin(5000),
    "RRH" -> new ReduceAndReconstructHelsinkiTimeout(5000),

    "RRST" -> RRS1PSimpleTermination,
    "RRMST" -> RRMinSimpleTermination,
    "RRHST" -> RRHelsinkiSimpleTermination,

    "RRRT" -> RRS1PRandomTermination,
    "RRMRT" -> RRMinRandomTermination,
    "RRHRT" -> RRHelsinkiRandomTermination,

    "Split" -> new CottonSplit(5000),
    "RBSplit" -> new RandomBoudouSplit(5000),
    "DBSplit" -> new DeterministicBoudouSplit(5000),
    "MSplit2" -> new TimeoutMultiSplit(2,5000),
    "MSplit3" -> new TimeoutMultiSplit(3,5000),
    "MSplit4" -> new TimeoutMultiSplit(4,5000),
    "RecS200ms" -> new InnerTimeoutRecSplit(200,5000),
    "RecS500ms" -> new InnerTimeoutRecSplit(500,5000),
    "RecS3" -> new DepthRecSplit(3,5000),
    "RecS5" -> new DepthRecSplit(5,5000),

    "PT" -> PruneTheory,
    
    //Congruence Algorithms
    "ArrayC" -> ArrayCongruence,
    "FibC" -> FibonacciCongruence,
    "PtC" -> ProofTreeCongruence,
    
    //Subsumptin Algorithms
    "TDS" -> TopDownSubsumption,
    "BUS" -> BottomUpSubsumptionTime,
    
    //Pebbling Algorithms
    "LCPebbler" -> new GenericBUPebbler(List("LastChild","InSub")),
    "ChildPebbler" -> new GenericBUPebbler(List("Children","InSub")),
    "LCPebblerTD" -> new GenericTDPebbler(List("LastChild","InSub")),
    "ChildrenPebblerTD" -> new GenericTDPebbler(List("Children","InSub")),
    "D1PebblerTD" -> new GenericTDPebbler(List("Distance1","InSub")),
    "D3PebblerTD" -> new GenericTDPebbler(List("Distance3","InSub")),
    "D1Pebbler" -> new GenericBUPebbler(List("Distance1","InSub")),
    "D3Pebbler" -> new GenericBUPebbler(List("Distance3","InSub")),
    "Distance5BU" -> new GenericBUPebbler(List("Distance5","InSub"))
    //All sort of decay pebblers, it would be nice to be able to use console input for parameters
//    "CDllmax" -> new ChildrenDecayPebbler(0.5, 1, (A: Seq[Double]) => A.max),
//    "CDllavg" -> new ChildrenDecayPebbler(0.5, 1, (A: Seq[Double]) => A.sum / A.size),
//    "CDlhmax" -> new ChildrenDecayPebbler(0.5, 7, (A: Seq[Double]) => A.max),
//    "CDlhavg" -> new ChildrenDecayPebbler(0.5, 7, (A: Seq[Double]) => A.sum / A.size),
//    "CDhlmax" -> new ChildrenDecayPebbler(3, 1, (A: Seq[Double]) => A.max),
//    "CDhlavg" -> new ChildrenDecayPebbler(3, 1, (A: Seq[Double]) => A.sum / A.size),
//    "CDhhmax" -> new ChildrenDecayPebbler(3, 7, (A: Seq[Double]) => A.max),
//    "CDhhavg" -> new ChildrenDecayPebbler(3, 7, (A: Seq[Double]) => A.sum / A.size),
//    "LCllmax" -> new LastChildOfDecayPebbler(0.5, 1, (A: Seq[Double]) => A.max),
//    "LCllavg" -> new LastChildOfDecayPebbler(0.5, 1, (A: Seq[Double]) => A.sum / A.size),
//    "LClhmax" -> new LastChildOfDecayPebbler(0.5, 7, (A: Seq[Double]) => A.max),
//    "LClhavg" -> new LastChildOfDecayPebbler(0.5, 7, (A: Seq[Double]) => A.sum / A.size),
//    "LChlmax" -> new LastChildOfDecayPebbler(3, 1, (A: Seq[Double]) => A.max),
//    "LChlavg" -> new LastChildOfDecayPebbler(3, 1, (A: Seq[Double]) => A.sum / A.size),
//    "LChhmax" -> new LastChildOfDecayPebbler(3, 7, (A: Seq[Double]) => A.max),
//    "LChhavg" -> new LastChildOfDecayPebbler(3, 7, (A: Seq[Double]) => A.sum / A.size),
//    "Dllmax" -> new LcoDCthenDistancePebbler(0.5, 1, (A: Seq[Double]) => A.max),
//    "Dllavg" -> new LcoDCthenDistancePebbler(0.5, 1, (A: Seq[Double]) => A.sum / A.size),
//    "Dlhmax" -> new LcoDCthenDistancePebbler(0.5, 7, (A: Seq[Double]) => A.max),
//    "Dlhavg" -> new LcoDCthenDistancePebbler(0.5, 7, (A: Seq[Double]) => A.sum / A.size),
//    "Dhlmax" -> new LcoDCthenDistancePebbler(3, 1, (A: Seq[Double]) => A.max),
//    "Dhlavg" -> new LcoDCthenDistancePebbler(3, 1, (A: Seq[Double]) => A.sum / A.size),
//    "Dhhmax" -> new LcoDCthenDistancePebbler(3, 7, (A: Seq[Double]) => A.max),
//    "Dhhavg" -> new LcoDCthenDistancePebbler(3, 7, (A: Seq[Double]) => A.sum / A.size),
//    "LC2llmax" -> new LastChildOfDecayPebblerNew(0.5, 1, (A: Seq[Double]) => A.max),
//    "LC2llavg" -> new LastChildOfDecayPebblerNew(0.5, 1, (A: Seq[Double]) => A.sum / A.size),
//    "LC2lhmax" -> new LastChildOfDecayPebblerNew(0.5, 7, (A: Seq[Double]) => A.max),
//    "LC2lhavg" -> new LastChildOfDecayPebblerNew(0.5, 7, (A: Seq[Double]) => A.sum / A.size),
//    "LC2hlmax" -> new LastChildOfDecayPebblerNew(3, 1, (A: Seq[Double]) => A.max),
//    "LC2hlavg" -> new LastChildOfDecayPebblerNew(3, 1, (A: Seq[Double]) => A.sum / A.size),
//    "LC2hhmax" -> new LastChildOfDecayPebblerNew(3, 7, (A: Seq[Double]) => A.max),
//    "LC2hhavg" -> new LastChildOfDecayPebblerNew(3, 7, (A: Seq[Double]) => A.sum / A.size)
  )
  
  trait fixNodes {
    def fixNode[P <: ProofNode[Sequent,P]](node: SequentProofNode, pivot: E, left: P, right: P, fixedLeft: SequentProofNode, fixedRight: SequentProofNode):SequentProofNode = {
      if ((left eq fixedLeft) && (right eq fixedRight)) node 
      else R(fixedLeft,fixedRight,pivot,true)
    }
      def fixNode[P <: ProofNode[Sequent,P]](node: SequentProofNode, pivot: E, left: P, right: P, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
        val fixedLeft  = fixedPremises.head
        val fixedRight = fixedPremises.last
        fixNode(node,pivot,left,right,fixedLeft,fixedRight)
    }
    def fixNode(node: SequentProofNode,fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      node match {
        case R(left, right, pivot, _) => {
          if (fixedPremises.isEmpty) node
          else {
            val fixedLeft  = fixedPremises.head
            val fixedRight = fixedPremises.last
            if ((left eq fixedLeft) && (right eq fixedRight)) node 
            else R(fixedLeft,fixedRight,pivot,true)
          }
        }
        case _ => node
      }
    }
  }
}


