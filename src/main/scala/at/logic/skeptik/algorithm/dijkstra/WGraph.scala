package at.logic.skeptik.algorithm.dijkstra

import scala.collection.immutable.HashSet
import scala.collection.immutable.{HashMap => Map}

class WGraph[T1,T2](v: Set[T1] = Set[T1](), e: Set[(T1,T2,T1)] = Set[(T1,T2,T1)](), w: Map[(T1,T2,T1),Int] = Map[(T1,T2,T1),Int](), adj: Map[T1,List[(T2,T1)]] = Map[T1,List[(T2,T1)]]()) {
  
  val vertices = v
  val edges = e
  val weights = w
  val adjacent = adj
    
  def addEdge(edge: (T1,T2,T1), weight: Int) = {
    new WGraph(vertices + edge._1 + edge._3, edges + edge, w + (edge -> weight), adjacent.updated(edge._1, adjacent.getOrElse(edge._1, List[(T2,T1)]()).+:((edge._2,edge._3))))
  }
  
  def addUndirectedEdge(edge: (T1,T2,T1), weight: Int):WGraph[T1,T2] = {
    val x = addEdge(edge,weight)
    x.addEdge((edge._3,edge._2,edge._1),weight)
  }
  
  override def toString = {
    "V: " + vertices.mkString(",") + "\n" + 
    "E: " + edges.map(e => (e._1,e._3)).mkString(",")
  }
}