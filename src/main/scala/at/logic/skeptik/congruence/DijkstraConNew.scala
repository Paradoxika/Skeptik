package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

abstract class DijkstraConNew(
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]], 
    rN: Map[E,Set[E]], 
    g: WEqGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends CongruenceNew(rep,cclass,lookup,lN,rN,g) {
  
  def newDijkstra: EquationDijkstra
  
  def explain(u: E, v: E): Option[EquationPath] = {
//    if (!resolveEarly) resolveDeducedQueue 
    val dij = newDijkstra
    val path = dij(u,v,g.graph)
    if (path.isEmpty) None else Some(path)
  }
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): CongruenceNew = {
    if (g.isInstanceOf[WEqGraph]) 
      new FibConNew(rep,cclass,lookup,lN,rN,g.asInstanceOf[WEqGraph])
    else
      this
  }
}

class FibConNew (
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]],
    rN: Map[E,Set[E]],
    g: WEqGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends DijkstraConNew(rep,cclass,lookup,lN,rN,g) {
  
  def newDijkstra: EquationDijkstra = {
    new FibonacciDijkstra
  }
}

object FibConNew {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new FibConNew(Map[E,E](),Map[E,Set[E]](),Map[(E,E),E](),Map[E,Set[E]](),Map[E,Set[E]](),new WEqGraph())
  }
}

class ArrayConNew (
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]],
    rN: Map[E,Set[E]],
    g: WEqGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends DijkstraConNew(rep,cclass,lookup,lN,rN,g) {
  
  def newDijkstra: EquationDijkstra = {
    new ArrayDijkstra
  }
}

object ArrayConNew {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new ArrayConNew(Map[E,E](),Map[E,Set[E]](),Map[(E,E),E](),Map[E,Set[E]](),Map[E,Set[E]](),new WEqGraph())
  }
}