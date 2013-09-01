package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.algorithm.compressor.Timeout


abstract class BoudouSplit
extends Split with AbstractSplitHeuristic {
  override def applyOnce(proof: Proof[N]) = {
    val (measures, measureSum) = computeMeasures(proof)
    def repeat(sum: Long):Proof[N] = {
      val selectedVariable = chooseVariable(measures, sum)
      val (left, right) = split(proof, selectedVariable)
      val compressedProof: Proof[N] = R(left, right, selectedVariable)
      if (compressedProof.size < proof.size) compressedProof
      else {
        val newSum = sum - measures(selectedVariable)
        if (newSum < 1) proof else {
          measures.remove(selectedVariable)
          repeat(newSum)
        }
      }
    }
    repeat(measureSum)
  }
}

class DeterministicBoudouSplit(val timeout: Int)
extends BoudouSplit with AdditivityHeuristic with DeterministicChoice with Timeout

class DeterministicPRSplit(val timeout: Int)
extends BoudouSplit with PivotRepetitionHeuristic with DeterministicChoice with Timeout

class DeterministicWDSplit(val timeout: Int)
extends BoudouSplit with WeightedDepthHeuristic with DeterministicChoice with Timeout

class DeterministicSSSplit(val timeout: Int)
extends BoudouSplit with SequentSizeHeuristic with DeterministicChoice with Timeout


class RandomBoudouSplit(val timeout: Int)
extends BoudouSplit with AdditivityHeuristic with RandomChoice with Timeout