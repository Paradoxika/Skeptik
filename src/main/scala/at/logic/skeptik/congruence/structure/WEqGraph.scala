package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression.E
import at.logic.skeptik.algorithm.dijkstra._
import scala.collection.mutable.{HashMap => MMap}

class WEqGraph(val graph: WGraph[E,EqLabel] = new WGraph[E,EqLabel]()) (implicit eqReferences: MMap[(E,E),EqW]) extends CongruenceGraph {
  
  def addEdge(u: E, v: E, eq: Option[EqW]): WEqGraph = {
    new WEqGraph(graph.addUndirectedEdge((u,EqLabel(eq.getOrElse(EqW(u,v)),Set[EquationPath]()),v), 1))
  }
  
  def addEdge(u: E, v: E, eqLabel: EqLabel, weight: Int): WEqGraph = {
    new WEqGraph(graph.addUndirectedEdge((u,eqLabel,v), weight))
  }
  
  override def toString = graph.toString
}

object WEqGraph {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new WEqGraph(new WGraph[E,EqLabel]())
  }
  
  def apply(graph: WGraph[E,EqLabel])(implicit eqReferences: MMap[(E,E),EqW]) = {
    new WEqGraph(graph)
  }
}