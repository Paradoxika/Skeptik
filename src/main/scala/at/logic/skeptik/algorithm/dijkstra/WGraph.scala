package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.{HashSet => MSet}
import scala.collection.immutable.HashSet
import scala.collection.immutable.{HashMap => Map}

/**
 * immutable class WGraph is structure for a weighted, labeled graph
 * 
 * type T1 is the type of vertices
 * type T2 is the type of labels
 * 
 * @param vertices set of vertices
 * @param edges set of edges (as triples (vertex, label, vertex))
 * @param weights weights of edges in Int
 * @param adjacent map of outgoing edges for vertices
 * 
 * keeping both e and adj is probably inefficient
 * 
 */
class WGraph[T1,T2](val vertices: Set[T1] = Set[T1](), 
    val edges: Set[(T1,T2,T1)] = Set[(T1,T2,T1)](), 
    val weights: Map[(T1,T2,T1),Int] = Map[(T1,T2,T1),Int](), 
    val adjacent : Map[T1,Set[(T2,T1)]] = Map[T1,Set[(T2,T1)]]()) {
  
  def addEdge(edge: (T1,T2,T1), weight: Int) = {
    val newAdj = adjacent.updated(edge._1, adjacent.getOrElse(edge._1, Set[(T2,T1)]()).+((edge._2,edge._3)))
    new WGraph(vertices + edge._1 + edge._3, edges + edge, weights + (edge -> weight), newAdj)
  }
  
  def removeEdge(edge: (T1,T2,T1)) = {
    val newAdj = adjacent.updated(edge._1, adjacent.getOrElse(edge._1, Set[(T2,T1)]()) - ((edge._2,edge._3)))
    val newW = weights - edge
    val newE = edges - edge
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
    val eS = "E: " + checked.map(e => (e._1,e._3,weights(e))).mkString(",")
    vS + "\n" + eS
  }
  
  def toStringDirected = {
    "V: " + vertices.mkString(",") + "\n" + 
    "E: " + edges.map(e => (e._1,e._3)).mkString(",")
  }
  
  override def toString = toStringUndirectedWeights
}