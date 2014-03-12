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
    val index: Int = Integer.MAX_VALUE, 
    val depth: Int = 0, 
    val numberOfChildren: Int = 0,
    val inSubProof: Int = 0,
    val lastChildOf: Int = 0, 
    val waitsForPremises: Int = 0, 
    val usesPebbles: Int = 0, 
    val childrenNotPebbled: Int = 0,
    val wasPebbled: Int = 0,
    val blocked: Boolean = false,
    val impact: Double = 0.0) {

  def changeInteger(which: Int, to: Int) = {
     new NodeInfo (
        if (which == 0) to else this.index,
        if (which == 1) to else this.depth,
        if (which == 2) to else this.numberOfChildren,
        if (which == 3) to else this.inSubProof,
        if (which == 4) to else this.lastChildOf,
        if (which == 5) to else this.waitsForPremises,
        if (which == 6) to else this.usesPebbles,
        if (which == 7) to else this.childrenNotPebbled,
        if (which == 8) to else this.wasPebbled,
        this.blocked,
        this.impact)
  }
  
  def changeIndex(to: Int) = changeInteger(0, to)
  
  def changeDepth(to: Int) = changeInteger(1, to)
  
  def changeNumberOfChildren(to: Int) = changeInteger(2, to)
  
  def changeInSubProof(to: Int) = changeInteger(3, to)
  
  def changeLastChildOf(to: Int) = changeInteger(4, to)
  
  def changeWaitsForPremises(to: Int) = changeInteger(5, to)
  
  def changeUsesPebbles(to: Int) = changeInteger(6, to)
  
  def changeChildrenNotPebbled(to: Int) = changeInteger(7, to)
  
  def changeWasPebbled(to: Int) = changeInteger(8, to)
  
  def changeBlocked(to: Boolean)  = {
     new NodeInfo (
        this.index,
        this.depth,
        this.numberOfChildren,
        this.inSubProof,
        this.lastChildOf,
        this.waitsForPremises,
        this.usesPebbles,
        this.childrenNotPebbled,
        this.wasPebbled,
        to,
        this.impact)
  }
  
  def changeImpact(to: Double) = {
    new NodeInfo (
        this.index,
        this.depth,
        this.numberOfChildren,
        this.inSubProof,
        this.lastChildOf,
        this.waitsForPremises,
        this.usesPebbles,
        this.childrenNotPebbled,
        this.wasPebbled,
        this.blocked,
        to)
  }
  override def toString:String = {
    "["+index + ", " + depth + ", " + numberOfChildren + ", " + inSubProof + ", " + waitsForPremises + ", " + usesPebbles + ", " + childrenNotPebbled + ", " + wasPebbled + ", " + blocked + ", " + impact +"]"
  }
}

final object EmptyNI extends NodeInfo()
//final object EmptyNI extends NodeInfo(Integer.MAX_VALUE,0,0.0,0,0,0,0,0,0)