package skeptik.algorithm.compressor

class Split
extends Function1[SequentProof,SequentProof] {
  
  def heuristic(node: SequentProof):Long = 
    ((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1

  def collectHeuristic(nodeCollection: ProofNodeCollection[SequentProof]) = {
    var heuristicSum = 0.toLong
    val heuristicMap = MMap[E,Long]()
    def visit(node: SequentProof) = node match {
      case CutIC(_,_,aux,_) =>
        val heuristicEval = heuristic(node)
        heuristicSum += heuristicEval
        heuristicMap.update(aux, heuristicMap.getOrElse(aux,0.toLong) + heuristicEval)
      case _ =>
    }
    nodeCollection.foreach(visit)
    (heuristicMap, heuristicSum)
  }

  private val rand = new scala.util.Random()

  def chooseALiteral(heuristicMap: Map[E,Long], heuristicSum: Long) = {
    val iterator = heuristicMap.toIterator
    def searchPos(left: Long):E = {
      val next = iterator.next
      if (next._2 < left && iterator.hasNext) searchPos(left - next._2) else next._1
    }
    searchPos(rand.nextLong(heuristicSum))
  }

  // TODO
}
