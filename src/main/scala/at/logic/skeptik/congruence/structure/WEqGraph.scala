package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression.E
import at.logic.skeptik.algorithm.dijkstra._
import scala.collection.mutable.{HashMap => MMap}

abstract class WEqGraph(val graph: WGraph[E,EqLabel] = new WGraph[E,EqLabel]()) (implicit eqReferences: MMap[(E,E),EqW]) extends CongruenceGraph {
  
  def newWEqGraph(graph: WGraph[E,EqLabel]): WEqGraph
  
  def newDijkstra: EquationDijkstra
  
  def explain(u: E, v: E)(implicit eqReferences: MMap[(E,E),EqW]): Option[EquationPath] = {
    val dij = newDijkstra
    val path = dij(u,v,graph)
    if (path.isEmpty) None else Some(path)
  }
  
  def addEdge(u: E, v: E, eq: Option[EqW]): WEqGraph = eq match {
    case None => {
      val paths = buildDD(u,None,v)
      val eqAll = paths.foldLeft(Set[EqW]())({(A,B) => 
        A union B.originalEqs
      })
      val weight = eqAll.size
      val eqLabel = EqLabel(EqW(u,v),paths)
      addEdge(u, v, eqLabel, weight)
    }
    case Some(e) => {
      newWEqGraph(graph.addUndirectedEdge((u,EqLabel(e,Set[EquationPath]()),v), 1))
    }
    
  }
  
  def addEdge(u: E, v: E, eqLabel: EqLabel, weight: Int): WEqGraph = {
     newWEqGraph(graph.addUndirectedEdge((u,eqLabel,v), weight))
  }
  
  override def toString = graph.toString
}

class FibonacciGraph(graph: WGraph[E,EqLabel] = new WGraph[E,EqLabel]()) (implicit eqReferences: MMap[(E,E),EqW]) extends WEqGraph(graph) {
  def newWEqGraph(graph: WGraph[E,EqLabel]): WEqGraph = {
    new FibonacciGraph(graph)
  }
  
  def newDijkstra: EquationDijkstra = {
    new FibonacciDijkstra
  }
}

class ArrayGraph(graph: WGraph[E,EqLabel] = new WGraph[E,EqLabel]()) (implicit eqReferences: MMap[(E,E),EqW]) extends WEqGraph(graph) {
  def newWEqGraph(graph: WGraph[E,EqLabel]): WEqGraph = {
    new ArrayGraph(graph)
  }
  
  def newDijkstra: EquationDijkstra = {
    new ArrayDijkstra
  }
}