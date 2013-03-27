package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.algorithm.compressor.Timeout


abstract class BoudouSplit
extends Split with AdditivityHeuristic {
  override def applyOnce(proof: Proof[N]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    def repeat(sum: Long):Proof[N] = {
      val selectedVariable = chooseVariable(literalAdditivity, sum)
      val (left, right) = split(proof, selectedVariable)
      val compressedProof: Proof[N] = R(left, right, _ == selectedVariable)
      if (compressedProof.size < proof.size) compressedProof
      else {
        val newSum = sum - literalAdditivity(selectedVariable)
        if (newSum < 1) proof else {
          literalAdditivity.remove(selectedVariable)
          repeat(newSum)
        }
      }
    }
    repeat(totalAdditivity)
  }
}

class DeterministicBoudouSplit(val timeout: Int)
extends BoudouSplit with DeterministicChoice with Timeout

class RandomBoudouSplit(val timeout: Int)
extends BoudouSplit with RandomChoice with Timeout