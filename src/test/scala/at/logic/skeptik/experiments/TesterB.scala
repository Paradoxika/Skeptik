package at.logic.skeptik.experiments

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.parser.ProofParserSPASS

import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{ SetSequent => IClause }
import at.logic.skeptik.algorithm.compressor.FOCollectEdgesUsingSafeLiterals
import at.logic.skeptik.algorithm.compressor.FOAbstractRPIAlgorithm
import at.logic.skeptik.algorithm.compressor.FOLowerUnits
import at.logic.skeptik.algorithm.compressor.FORecyclePivotsWithIntersection
import at.logic.skeptik.algorithm.compressor.FOCollectEdgesUsingSafeLiterals
import at.logic.skeptik.algorithm.compressor.checkProofEquality
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.algorithm.compressor.FOCollectEdgesUsingSafeLiterals
import at.logic.skeptik.algorithm.compressor.checkProofEquality
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}

object TesterB extends FOAbstractRPIAlgorithm with FOCollectEdgesUsingSafeLiterals with checkProofEquality {
  def apply(proof: Proof[SequentProofNode]) = {
    proof
    //  FORecyclePivots(proof)
  }
  protected def computeSafeLiterals(proof: SequentProofNode,
                                    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
                                    edgesToDelete: FOEdgesToDelete): IClause = {
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof) } match {
      case Nil =>
        if (!childrensSafeLiterals.isEmpty) edgesToDelete.markBothEdges(proof)
        proof.conclusion.toSetSequent
      case h :: t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) =>
          {
            acc intersect safeLiteralsFromChild(v, proof, edgesToDelete)
          }
        }
    }
  }
  
  
  def main(args: Array[String]): Unit = {    


    val proof = ProofParserSPASS.read("D:\\Git Repositories\\Skeptik\\examples\\proofs\\SPASS\\aicom-ce.spass")     
      
    println(proof)
    val cProof = FORecyclePivotsWithIntersection(proof)
    println(cProof)

    
    
  }
}



