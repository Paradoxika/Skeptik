package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.compressor.split._
import at.logic.skeptik.algorithm.compressor.subsumption._
import at.logic.skeptik.algorithm.compressor.pebbler._
import at.logic.skeptik.expression.E
import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.algorithm.compressor.subsumption.RecycleUnits

// Algorithm names should contain only alphanumeric characters

// ToDo: the name of an algorithm should be a property defined in the algorithm's class

package object compressor {
  val algorithms = Map(
    "DAGify" -> DAGify,
    "ET" -> EliminateTautologies,
    "RU" -> RecycleUnits,
    "RP" -> RecyclePivots,
    "RPI" -> RecyclePivotsWithIntersection,
    "RPC" -> RecyclePivotsWithConclusionSequent,
    "LU" -> LowerUnits,
    "LUniv" -> LowerUnivalents,
    "RPI3LU" -> IdempotentThreePassLowerUnits,
    "LUnivRPI" -> IdempotentLowerUnivalentsAfterRecyclePivots,
    "RPI3LUniv" -> LowerUnivalentsBeforeRecyclePivots,
    "RR" -> new ReduceAndReconstruct(5000),
    "RRlm" -> new RRWithLowerMiddle(5000),
    "lmA2" -> new LowerMiddleA2(5000),
    "Split" -> new CottonSplit(30000),
    "RBSplit" -> new RandomBoudouSplit(30000),
    "DBSplit" -> new DeterministicBoudouSplit(5000),
    "MSplit2" -> new TimeoutMultiSplit(2,5000),
    "MSplit3" -> new TimeoutMultiSplit(3,3000),
    "MSplit4" -> new TimeoutMultiSplit(4,5000),
    "RecS200ms" -> new InnerTimeoutRecSplit(200,5000),
    "RecS500ms" -> new InnerTimeoutRecSplit(500,5000),
    "RecS3" -> new DepthRecSplit(3,5000),
    "RecS5" -> new DepthRecSplit(5,5000),
    "TDS" -> TopDownSubsumption,
    "GP" -> RemoveMostPebbles,
    "BUP" -> LastChildOfBUPebbler,
    "P1" -> new GenericBUPebbler(List("LastChild","Children","ProofSize")),
    "P2" -> new GenericBUPebbler(List("SubProofPebbled","LastChild","Children","ProofSize")),
    "CDllmin" -> new ChildrenDecayPebbler(0.5, 1, (A: Seq[Double]) => A.min),
    "CDllavg" -> new ChildrenDecayPebbler(0.5, 1, (A: Seq[Double]) => A.sum / A.size),
    "CDlhmin" -> new ChildrenDecayPebbler(0.5, 7, (A: Seq[Double]) => A.min),
    "CDlhavg" -> new ChildrenDecayPebbler(0.5, 7, (A: Seq[Double]) => A.sum / A.size),
    "CDhlmin" -> new ChildrenDecayPebbler(3, 1, (A: Seq[Double]) => A.min),
    "CDhlavg" -> new ChildrenDecayPebbler(3, 1, (A: Seq[Double]) => A.sum / A.size),
    "CDhhmin" -> new ChildrenDecayPebbler(3, 7, (A: Seq[Double]) => A.min),
    "CDhhavg" -> new ChildrenDecayPebbler(3, 7, (A: Seq[Double]) => A.sum / A.size),
    "LCllmax" -> new LastChildOfDecayPebbler(0.5, 1, (A: Seq[Double]) => A.max),
    "LCllavg" -> new LastChildOfDecayPebbler(0.5, 1, (A: Seq[Double]) => A.sum / A.size),
    "LClhmin" -> new LastChildOfDecayPebbler(0.5, 7, (A: Seq[Double]) => A.max),
    "LClhavg" -> new LastChildOfDecayPebbler(0.5, 7, (A: Seq[Double]) => A.sum / A.size),
    "LChlmin" -> new LastChildOfDecayPebbler(3, 1, (A: Seq[Double]) => A.max),
    "LChlavg" -> new LastChildOfDecayPebbler(3, 1, (A: Seq[Double]) => A.sum / A.size),
    "LChhmin" -> new LastChildOfDecayPebbler(3, 7, (A: Seq[Double]) => A.max),
    "LChhavg" -> new LastChildOfDecayPebbler(3, 7, (A: Seq[Double]) => A.sum / A.size),
    "Dllmax" -> new LcoDCthenDistancePebbler(0.5, 1, (A: Seq[Double]) => A.max),
    "Dllavg" -> new LcoDCthenDistancePebbler(0.5, 1, (A: Seq[Double]) => A.sum / A.size),
    "Dlhmin" -> new LcoDCthenDistancePebbler(0.5, 7, (A: Seq[Double]) => A.max),
    "Dlhavg" -> new LcoDCthenDistancePebbler(0.5, 7, (A: Seq[Double]) => A.sum / A.size),
    "Dhlmin" -> new LcoDCthenDistancePebbler(3, 1, (A: Seq[Double]) => A.max),
    "Dhlavg" -> new LcoDCthenDistancePebbler(3, 1, (A: Seq[Double]) => A.sum / A.size),
    "Dhhmin" -> new LcoDCthenDistancePebbler(3, 7, (A: Seq[Double]) => A.max),
    "Dhhavg" -> new LcoDCthenDistancePebbler(3, 7, (A: Seq[Double]) => A.sum / A.size),
    "TestP" -> new InSubThenUsesPebblesPebbler(3, 7, (A: Seq[Double]) => A.max)
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


