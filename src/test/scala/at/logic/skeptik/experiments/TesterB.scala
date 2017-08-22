package at.logic.skeptik.experiments

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.parser.ProofParserSkeptikOutput

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


//    val proof = ProofParserSPASS.read("D:\\Git Repositories\\Skeptik\\examples\\proofs\\SPASS\\aicom-ce.spass")     
////          val proof = ProofParserSPASS.read("D:\\Git Repositories\\Skeptik\\examples\\proofs\\SPASS\\aicom-ceb.spass")     
//
//    println(proof)
//    val cProof = FORecyclePivotsWithIntersection(proof)
//    println(cProof)

        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 15-27-23 EST 2016-proof-174.txt")//

        println(proof)
              println(" Compression starting...")

      val oSize = proof.toSeq.size
      
      var LUfail = false
      var RPIfail = false
      var LURPIfail = false
      var RPILUfail = false

      var RPIfailAfterLU = false
      var LUfailAfterRPI = false
      
      var luFails = 0
      var rpiFails = 0
      var rpiluFails = 0
      var lurpiFails = 0

      val luStartTime = System.nanoTime()

      val luProof = try {
        val p = FOLowerUnits(proof)
        if(p.root.conclusion.ant.size != 0 || p.root.conclusion.suc.size != 0){
          LUfail = true
          luFails = luFails +1
          proof
        } else {
         // printCompressedProof(p,collectedProofPrefix,collectedProofSuffix,h,"lu")
          p
        }
      } catch {
        case e: Exception => {
          LUfail = true
          luFails = luFails + 1
          proof
        }
        case a: AssertionError => {
          LUfail = true
          luFails = luFails + 1
          proof
        }
      }
      val luFinishTime = System.nanoTime()

            val afterLUsize = proof.toSeq.size
      assert(afterLUsize == oSize)

      println("LU PROOF: ")
      println(luProof)


      val rpiLUStartTime = System.nanoTime()
      val rpiLUProof = try {
        val p = FORecyclePivotsWithIntersection(luProof)
        if(p.root.conclusion.ant.size != 0 || p.root.conclusion.suc.size != 0){
          RPILUfail = true //definitely want to report fail here
          luProof
        } else {
         // printCompressedProof(p,collectedProofPrefix,collectedProofSuffix,h,"rpilu")          
          p
        }                
      } catch {
        case e: Exception => {
          if (LUfail) { RPILUfail = true 
          } else { RPIfailAfterLU = true }
          luProof
        }
        case a: AssertionError => {
          if (LUfail) { RPILUfail = true  
          } else { RPIfailAfterLU = true }
          luProof
        }
      }
      val rpiLUFinishTime = System.nanoTime()
    
      println("RPILU PROOF:")
      println(rpiLUProof)
      
      println(LUfail)
      println(RPILUfail)
      
  }
}



