package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.dijkstra._
import scala.collection.mutable.{StringBuilder, HashMap => MMap}
import scala.collection.mutable.ListBuffer

case class ProofForest(next: Map[E,(E,Option[EqW])] = Map[E,(E,Option[EqW])](), rootSize: Map[E,Int] = Map[E,Int]()) extends CongruenceGraph {
  def addEdge(u: E, v: E, eq: Option[EqW]) = {
    val uR = root(u)
    val vR = root(v)
    if (uR != vR) {
      val uIn = if (!rootSize.isDefinedAt(uR)) ProofForest(next,rootSize + (u -> 1)) else this
      val vIn = if (!rootSize.isDefinedAt(v)) ProofForest(uIn.next,uIn.rootSize +(v -> 1)) else uIn
      if (vIn.rootSize(uR) > vIn.rootSize(vR)) {
        vIn.insertEdge(u,uR,v,vR,eq)
      }
      else {
        vIn.insertEdge(v,vR,u,uR,eq)
      }
    }
    else this
  }
  
  def root(u: E) = {
    var node = u
    while (next.isDefinedAt(node)) {
      node = next(node)._1
    }
    node
  }
  
  def reversePathList(orig: List[(E,Option[EqW],E)]) = {
    orig.foldLeft(List[(E,Option[EqW],E)]())({(A,B) => 
      A.+:((B._3,B._2,B._1))
    })
  }
  
  def ncaPath(u: E, v: E) = {
    val p1 = rootPath(u)
    val p2 = rootPath(v)
    p1.diff(p2) ++ reversePathList(p2.diff(p1))
  }
  
  def explainAlongPath(path: List[(E,Option[EqW],E)]): EquationPath = {
//    println(path)
    val (t1,eq,t2) = path.head
    val eqCheat = eq.getOrElse(EqW(t1,t2,MMap[(E,E),EqW]())) //Probably causing bugs!
    val deduceTrees = eq match {
      case None => {
        (t1,t2) match {
          case (App(u1,v1),App(u2,v2)) => {
            (explain(u1,u2),explain(v1,v2)) match {
              case (Some(dd1),Some(dd2)) => {
//                println("expl for " + (u1,u2) + ": " + dd1)
//                println("expl for " + (v1,v2) + ": " + dd2)
                Some(dd1,dd2)
              }
              case _ => {
//                println("here for " + (t1,t2) + " : " + explain(v1,v2))
                None //failure
              }
            }
          }
          case _ => None //failure
        }
      }
      case Some(_) => None
    }
    
    val eqL = EqLabel(eqCheat,deduceTrees)
    val nextEdge = if (path.size > 1)
      explainAlongPath(path.tail)
    else {
      new EquationPath(t2,None)
    }
    val eqEdge = EqTreeEdge(nextEdge,eqL)
    new EquationPath(t1,Some(eqEdge))
  }
  
  def explain(u: E, v: E): Option[EquationPath] = {
    val path = ncaPath(u,v) 
    if (path.isEmpty) {
      if (u == v) Some(new EquationPath(u,None))
      else None
    }
    else Some(explainAlongPath(path))
  }
  
  def rootPath(u: E) = {
    val path = ListBuffer[(E,Option[EqW],E)]()
    var node = u
    while (next.isDefinedAt(node)) {
      val nn = next(node)
      path.+=((node,nn._2,nn._1))
      node = nn._1
    }
    path.toList
  }
  
  private def insertEdge(u: E, uRoot: E, v: E, vRoot: E, eq: Option[EqW]): ProofForest = {
//    println("adding " + v + " to " + u)
    val reversed = reverseToRoot(v)
    val finalSize = reversed.rootSize.updated(uRoot,reversed.rootSize(uRoot) + reversed.rootSize(vRoot)) - v
    val finalNext = reversed.next.updated(v, (u,eq))
    ProofForest(finalNext,finalSize)
  }
  
  def reverseToRoot(u: E): ProofForest = {
//    println("reversing " + u)
    val path = rootPath(u)
    val revNext = path.foldLeft(next)({(A,B) =>
      val (node1,eq,node2) = B
      A.updated(node2,(node1,eq))
    })
    val finalNext = revNext - u
    ProofForest(finalNext,rootSize)
  }
  
  def printNode(u: E) = {
    var node = u
    var out = new StringBuilder
    while (next.isDefinedAt(node)) {
      out.append(node +" -> ")
      node = next(node)._1
    }
    out.append(node.toString)
  }
}