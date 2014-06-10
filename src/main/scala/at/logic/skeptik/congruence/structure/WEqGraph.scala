package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression.E
import at.logic.skeptik.algorithm.dijkstra._
import scala.collection.mutable.{HashMap => MMap}

abstract class WEqGraph(
    val graph: WGraph[E,EqLabel] = new WGraph[E,EqLabel](),
    lazyEdges: Map[(E,E),Option[EqW]]) 
    (implicit eqReferences: MMap[(E,E),EqW]) 
      extends CongruenceGraph(lazyEdges) {

  def newWEqGraph(graph: WGraph[E,EqLabel],edges: Map[(E,E),Option[EqW]]): WEqGraph
  
  def newDijkstra: EquationDijkstra
  
  def explain(u: E, v: E)(implicit eqReferences: MMap[(E,E),EqW]): Option[EquationPath] = {
    val realGraph = lazyEdges.foldLeft(this)({(A,B) => 
//      println("adding " + (B._1._1, B._1._2, B._2) + " lE: " + A.asInstanceOf[CongruenceGraph].lazyEdges.mkString(","))
      A.addEdge(B._1._1, B._1._2, B._2)
    })
    val dij = newDijkstra
    val path = dij(u,v,realGraph.graph)
    Some(path)
  }

  def addEdge(u: E, v: E, eq: Option[EqW]): WEqGraph = {
    val newLazy = lazyEdges - ((u,v)) - ((v,u))
    val newG = newWEqGraph(graph,newLazy)
    eq match {
      case None => {
//        println("here")
        val paths = newG.buildDD(u,None,v)
        
        val eqAll = paths.foldLeft(Set[EqW]())({(A,B) => 
          A union B.originalEqs
        })
        val weight = eqAll.size
        val eqLabel = EqLabel(EqW(u,v),paths)
        
        newG.addEdge(u, v, eqLabel, weight)
      }
      case Some(e) => {
//        println("here_2")
        newG.addEdge(u, v, EqLabel(e,Set[EquationPath]()), 1)
      }
    }
  }
  
  def addEdge(u: E, v: E, eqLabel: EqLabel, weight: Int): WEqGraph = {
     newWEqGraph(graph.addUndirectedEdge((u,eqLabel,v), weight),lazyEdges)
  }
  
  override def toString = graph.toString
}

class FibonacciGraph(graph: WGraph[E,EqLabel] = new WGraph[E,EqLabel](), lazyEdges: Map[(E,E),Option[EqW]] = Map[(E,E),Option[EqW]]()) (implicit eqReferences: MMap[(E,E),EqW]) extends WEqGraph(graph,lazyEdges) {
  def newWEqGraph(graph: WGraph[E,EqLabel],edges: Map[(E,E),Option[EqW]]): WEqGraph = {
    new FibonacciGraph(graph,edges)
  }
  
  def newGraph(edges: Map[(E,E),Option[EqW]]): CongruenceGraph = {
    new FibonacciGraph(graph,edges)
  }
  
  def newDijkstra: EquationDijkstra = {
    new FibonacciDijkstra
  }
}

class ArrayGraph(graph: WGraph[E,EqLabel] = new WGraph[E,EqLabel](), lazyEdges: Map[(E,E),Option[EqW]] = Map[(E,E),Option[EqW]]()) (implicit eqReferences: MMap[(E,E),EqW]) extends WEqGraph(graph, lazyEdges) {
  def newWEqGraph(graph: WGraph[E,EqLabel],edges: Map[(E,E),Option[EqW]]): WEqGraph = {
    new ArrayGraph(graph,edges)
  }
  
  def newGraph(edges: Map[(E,E),Option[EqW]]): CongruenceGraph = {
    new ArrayGraph(graph,edges)
  }
  
  def newDijkstra: EquationDijkstra = {
    new ArrayDijkstra
  }
}