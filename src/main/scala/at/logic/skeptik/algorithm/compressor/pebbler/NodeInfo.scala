package at.logic.skeptik.algorithm.compressor.pebbler

/**NodeInfo represents information of a node for sorting nodes in top down or bottom up pebbling algorithms
 * all descriptions reference the corresponding node as n
 * - index i: in the original proof and in a bottom up traversal, the node was visited at the i'th iteration
 * - depth: number of nodes on the shortest path between the proof root and n
 * - numberOfChildren: the amount of children nodes of n
 * - lastChildOf: the amount of nodes of which n is the last child that is visited in a top down traversal
 * - waitForPremises: the number of currently unpebbled premises
 *    Especially interesting when the value is set to 1, because then n can be pebbled
 * - usesPebbles: upper bound of pebbles that are currently used for n and its premises
 * - childrenNotPebbled: number of children nodes of n, that have not yet been visited. 
 *    Especially interesting when the value is set to 1, 
 *    because then when pebbling another child of n, the pebbles of n can be removed
 * 
 * These objects might be too heavy for a fast algorithm. 
 * If one is only interested in certain data, then computing this separately will be more efficient.
 */

class NodeInfo(
    val index: Int, 
    val depth: Int, 
    val numberOfChildren: Int, 
    var lastChildOf: Int, 
    var waitsForPremises: Int, 
    var usesPebbles: Int, 
    var childrenNotPebbled: Int) {
  
  def incLCO = 
    lastChildOf = lastChildOf + 1
    
  override def toString:String = {
    "["+index+", " + lastChildOf + ", " + numberOfChildren +"]"
  }
}

final object EmptyNI extends NodeInfo(Integer.MAX_VALUE,0,0,0,0,0,0)