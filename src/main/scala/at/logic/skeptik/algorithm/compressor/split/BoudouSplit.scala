package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.algorithm.compressor.Timeout

import annotation.tailrec


abstract class BoudouSplit
extends Split with AdditivityHeuristic {
  override def applyOnce(proof: Proof[N]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)

    @tailrec
    def repeat(sum: Long):Proof[N] = 
      if (sum < 1) proof else {
        val selectedVariable = chooseVariable(literalAdditivity, sum)
        val (left, right) = split(proof, selectedVariable)
        val compressedProof: Proof[N] = R(left, right, selectedVariable)
        if (compressedProof.size < proof.size) compressedProof
        else {
          val newSum = sum - literalAdditivity(selectedVariable)
          literalAdditivity.remove(selectedVariable)
          repeat(newSum)
        }
      }

    repeat(totalAdditivity)
  }
}

class DeterministicBoudouSplit(val timeout: Int)
extends BoudouSplit with DeterministicChoice with Timeout

class RandomBoudouSplit(val timeout: Int)
extends BoudouSplit with RandomChoice with Timeout
