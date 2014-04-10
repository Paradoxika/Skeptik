package at.logic.skeptik.algorithm.dijkstra

class PathTree[T1,T2](v: T1, pred: Option[(PathTree[T1,T2],Set[T2])]) {
  
  override def toString = {
    if (pred.isDefined) {
      v + " <" + pred.get._2 + "- " + pred.get._1
//      v + ", " + pred.get._1
    }
    else {
      v.toString
    }
  }
  
  def collectVertices: List[T1] = {
    if (pred.isDefined) {
      v +: pred.get._1.collectVertices
    }
    else {
      List(v)
    }
  }
  
  def depth: Int = {
    if (pred.isDefined) {
      1 + pred.get._1.depth
    }
    else {
      0
    }
  }
//  def sumWeights: Int = {
//    if (pred.isDefined) {
//      pred.get._3 + pred.get._1.sumWeights
//    }
//    else {
//      0
//    }
//  }
  
  def collectLabels: Set[T2] = {
    if (pred.isDefined) {
      val z = pred.get._2
      val y = pred.get._1.collectLabels
      val x = y union z
//      println("label at " + v + " ~ " + y + " + " + z + " <==> " + x)
      x
    }
    else {
      Set()
    }
  }
}