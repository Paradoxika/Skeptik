package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof._

/* Base class for proof compression algorithms
 */
abstract class ProofCompressor[N <: ProofNode[Judgment,N]] extends (Proof[N] => Proof[N])
