package at.logic.skeptik.algorithm.dijkstra

import at.logic.skeptik.expression._

//case class Selfie[T1,T2] extends PathTree with SelfPathTree[T1,T2]

//case class SelfPathTree[VERT,EDGE](v: VERT, pred: Option[(SelfPathTree[VERT,EDGE],(EDGE,Option[(SelfPathTree[VERT,EDGE],SelfPathTree[VERT,EDGE])]))])
//  extends PathTree[VERT,Option[(SelfPathTree[VERT,EDGE],(EDGE,Option[(SelfPathTree[VERT,EDGE],SelfPathTree[VERT,EDGE])]))],SelfPathTree[VERT,EDGE]](v,pred) {

//case class EquationTree(override val v: E, override val pred: EqTreeEdge) 
//  extends PathTree[E,Option[(EquationTree,(App,Option[(EquationTree,EquationTree)]))],EquationTree,(App,Option[(EquationTree,EquationTree)])](v,pred){

case class EquationTree(val v: E, val pred: Option[(EquationTree,(App,Option[(EquationTree,EquationTree)]))]) {
//  extends PathTree[E,Option[(EquationTree,(App,Option[(EquationTree,EquationTree)]))],EquationTree,(App,Option[(EquationTree,EquationTree)])](v,pred){

  
  def eq: Option[App] = pred match {
    case Some(pr) => {
      Some(pr._2._1)
    }
    case None => None
  }
  
  def allEqs: Set[App] = pred match {
    case Some(pr) => {
      pr._1.pathEqs + pr._2._1 ++ deduceEqs
    }
    case None => {
      Set()
    }
  }
  
  def pathEqs: Set[App] = pred match {
    case Some(pr) => {
      pr._1.pathEqs + pr._2._1
    }
    case None => {
      Set()
    }
  }
  
  def deduceEqs: Set[App] = {
    val lEqs = leftExpl match {
      case Some(l) => l.pathEqs
      case None => Set()
    }
    val rEqs = rightExpl match {
      case Some(r) => r.pathEqs
      case None => Set()
    }
    lEqs ++ rEqs
  }
  
  def predTree: Option[EquationTree] = pred match {
    case Some(pr) => Some(pr._1)
    case None => None
  }
  
  def leftExpl: Option[EquationTree] = pred match {
    case Some(pr) => pr._2._2 match {
      case Some((l,r)) => Some(l)
      case None => None
    }
    case None => None
  }
  
  def rightExpl: Option[EquationTree] = pred match {
    case Some(pr) => pr._2._2 match {
      case Some((l,r)) => Some(r)
      case None => None
    }
    case None => None
  }
  
    def collectLabels: Set[EqLabel] = pred match {
      case Some(pr) => {
        val z = pr._2
        val y = pr._1.collectLabels
        val x = y + z
  //      println("label at " + v + " ~ " + y + " + " + z + " <==> " + x)
        x
      }
      case None => {
        Set()
      }
    }
}

//object PathTree[T1,T2] {
//  def apply(v: T1, pred: T2){
//    
//  }
//}

/*****
 * T1: vertix label
 * T2: edge label
 * T3: successor type
 */

//abstract class PathTree[T1,T2 <: Option[(T3,T4)],T3 <: PathTree[T1,T2,T3,T4],T4](val v: T1, val pred: T2) {
//  
//  override def toString = {
//    if (pred.isDefined) {
//      v + " <" + pred.get._2 + "- " + pred.get._1
////      v + ", " + pred.get._1
//    }
//    else {
//      v.toString
//    }
//  }
//  
//  def toProof: Boolean = {
//    if (pred.isDefined) {
//      val x = (pred.get._1.v == v)
//      if (!x) println(v + " is not equal to " + pred.get._1.v)
//      else println(v + " is equal to " + pred.get._1.v)
//      x && pred.get._1.toProof
//    }
//    else true
//  }
//  
//  def collectVertices: List[T1] = {
//    if (pred.isDefined) {
//      v +: pred.get._1.collectVertices
//    }
//    else {
//      List(v)
//    }
//  }
//  
//  def depth: Int = {
//    if (pred.isDefined) {
//      1 + pred.get._1.depth
//    }
//    else {
//      0
//    }
//  }
////  def sumWeights: Int = {
////    if (pred.isDefined) {
////      pred.get._3 + pred.get._1.sumWeights
////    }
////    else {
////      0
////    }
////  }
//
//  def lastLabel: Option[T4] = {
//    if (pred.isDefined) {
//      Some(pred.get._2)
//    }
//    else None
//  }
//  
//  def collectLabels: Set[T4] = {
//    if (pred.isDefined) {
//      val z = pred.get._2
//      val y = pred.get._1.collectLabels
//      val x = y + z
////      println("label at " + v + " ~ " + y + " + " + z + " <==> " + x)
//      x
//    }
//    else {
//      Set()
//    }
//  }
//}