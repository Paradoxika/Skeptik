package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.algorithm.compressor.Timeout

class CottonSplit(val timeout: Int)
extends Split with AdditivityHeuristic with RandomChoice with Timeout
