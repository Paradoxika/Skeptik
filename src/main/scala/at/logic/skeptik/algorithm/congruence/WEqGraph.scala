package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.E
import at.logic.skeptik.algorithm.dijkstra._
import scala.collection.mutable.{HashMap => MMap}

class WEqGraph(val graph: WGraph[E,EqLabel] = new WGraph[E,EqLabel]()) extends CongruenceGraph {
  def addEdge(u: E, v: E, eq: Option[EqW]): WEqGraph = {
    new WEqGraph(graph.addUndirectedEdge((u,EqLabel(eq.getOrElse(EqW(u,v,MMap[(E,E),EqW]())),None),v), 1))
  }
  
  def addEdge(u: E, v: E, eqLabel: EqLabel, weight: Int): WEqGraph = {
    new WEqGraph(graph.addUndirectedEdge((u,eqLabel,v), weight))
  }
  
  override def toString = graph.toString
}