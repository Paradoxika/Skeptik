package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.compressor.split._
import at.logic.skeptik.algorithm.compressor.subsumption._
import at.logic.skeptik.algorithm.compressor.reduceAndReconstruct._

import at.logic.skeptik.expression.E
import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.proof.sequent.lk.R

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

    "RR" -> new ReduceAndReconstructS1P(5000),
    "RRM" -> new ReduceAndReconstructMin(5000),
    "RRC" -> new ReduceAndReconstructC1P(5000),
    "RRlm" -> new ReduceAndReconstructMiddleLowerTimeout(5000),
    "RRH" -> new ReduceAndReconstructHelsinkiTimeout(5000),

    "RRST" -> RRS1PSimpleTermination,
    "RRMST" -> RRMinSimpleTermination,
    "RRCST" -> RRC1PSimpleTermination,
    "RRlmST" -> RRMiddleLowerSimpleTermination,
    "RRHST" -> RRHelsinkiSimpleTermination,

    "RROT" -> RRS1POverTermination,
    "RRMOT" -> RRMinOverTermination,
    "RRCOT" -> RRC1POverTermination,
    "RRlmOT" -> RRMiddleLowerOverTermination,
    "RRHOT" -> RRHelsinkiOverTermination,

    "RRROT" -> RRS1PRandomA2,
    "RRMROT" -> RRMinRandomA2,
    "RRCROT" -> RRC1PRandomA2,
    "RRlmROT" -> RRMiddleLowerRandomA2,
    "RRHROT" -> RRHelsinkiRandomA2,

    "RRROTA" -> RRS1PRandomA2Alt,
    "RRMROTA" -> RRMinRandomA2Alt,
    "RRCROTA" -> RRC1PRandomA2Alt,
    "RRlmROTA" -> RRMiddleLowerRandomA2Alt,
    "RRHROTA" -> RRHelsinkiRandomA2Alt,

    "Split" -> new CottonSplit(30000),
    "RBSplit" -> new RandomBoudouSplit(30000),
    "DBSplit" -> new DeterministicBoudouSplit(30000),
    "MSplit2" -> new TimeoutMultiSplit(2,5000),
    "MSplit3" -> new TimeoutMultiSplit(3,5000),
    "MSplit4" -> new TimeoutMultiSplit(4,5000),
    "RecS200ms" -> new InnerTimeoutRecSplit(200,5000),
    "RecS500ms" -> new InnerTimeoutRecSplit(500,5000),
    "RecS3" -> new DepthRecSplit(3,5000),
    "RecS5" -> new DepthRecSplit(5,5000),

    "TDS" -> TopDownSubsumption,
    "GP" -> RemoveMostPebbles,
    "BUP" -> LastChildOfBUPebbler
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


