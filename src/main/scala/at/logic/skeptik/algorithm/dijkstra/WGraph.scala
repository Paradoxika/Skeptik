package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.{HashSet => MSet}
import scala.collection.immutable.HashSet
import scala.collection.immutable.{HashMap => Map}

class WGraph[T1,T2](v: Set[T1] = Set[T1](), e: Set[(T1,T2,T1)] = Set[(T1,T2,T1)](), w: Map[(T1,T2,T1),Int] = Map[(T1,T2,T1),Int](), adj: Map[T1,Set[(T2,T1)]] = Map[T1,Set[(T2,T1)]]()) {
  
  val vertices = v
  val edges = e
  val weights = w
  val adjacent = adj
    
  def addEdge(edge: (T1,T2,T1), weight: Int) = {
    val newAdj = adjacent.updated(edge._1, adjacent.getOrElse(edge._1, Set[(T2,T1)]()).+((edge._2,edge._3)))
//    println("newAdj after adding " + edge + " " + newAdj)
    new WGraph(vertices + edge._1 + edge._3, edges + edge, w + (edge -> weight), newAdj)
  }
  
  def removeEdge(edge: (T1,T2,T1)) = {
    val newAdj = adjacent.updated(edge._1, adjacent.getOrElse(edge._1, Set[(T2,T1)]()) - ((edge._2,edge._3)))
    val newW = w - edge
    val newE = e - edge
    new WGraph(vertices, newE, newW, newAdj)
  }
  
  def removeUndirectedEdge(edge: (T1,T2,T1)) = {
    val x = removeEdge(edge)
    x.removeEdge((edge._3,edge._2,edge._1))
  }
  
  def addUndirectedEdge(edge: (T1,T2,T1), weight: Int):WGraph[T1,T2] = {
    val x = addEdge(edge,weight)
    x.addEdge((edge._3,edge._2,edge._1),weight)
  }
  
  def toStringUndirected = {
    val vS = "V: " + vertices.mkString(",")
    val checked = MSet[(T1,T2,T1)]()
    edges.foreach(e => if (!checked.contains(e._3,e._2,e._1)) checked += e)
    val eS = "E: " + checked.map(e => (e._1,e._3)).mkString(",")
    vS + "\n" + eS
  }
  
  def toStringUndirectedWeights = {
    val vS = "V: " + vertices.mkString(",")
    val checked = MSet[(T1,T2,T1)]()
    edges.foreach(e => if (!checked.contains(e._3,e._2,e._1)) checked += e)
    val eS = "E: " + checked.map(e => (e._1,e._3,w(e))).mkString(",")
    vS + "\n" + eS
  }
  
  def toStringDirected = {
    "V: " + vertices.mkString(",") + "\n" + 
    "E: " + edges.map(e => (e._1,e._3)).mkString(",")
  }
  
  override def toString = toStringUndirectedWeights
}