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
  
  def explain(u: E, v: E): Option[EquationPath] = {
    g.explain(u, v)
  }
}

class FibConNew (
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]],
    rN: Map[E,Set[E]],
    g: FibonacciGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends DijkstraConNew(rep,cclass,lookup,lN,rN,g) {
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): CongruenceNew = {
    if (g.isInstanceOf[FibonacciGraph]) 
      new FibConNew(rep,cclass,lookup,lN,rN,g.asInstanceOf[FibonacciGraph])
    else
      this
  }
}

object FibConNew {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new FibConNew(Map[E,E](),Map[E,Set[E]](),Map[(E,E),E](),Map[E,Set[E]](),Map[E,Set[E]](),new FibonacciGraph())
  }
}

class ArrayConNew (
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]],
    rN: Map[E,Set[E]],
    g: ArrayGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends DijkstraConNew(rep,cclass,lookup,lN,rN,g) {
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): CongruenceNew = {
    if (g.isInstanceOf[ArrayGraph]) 
      new ArrayConNew(rep,cclass,lookup,lN,rN,g.asInstanceOf[ArrayGraph])
    else
      this
  }
}

object ArrayConNew {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new ArrayConNew(Map[E,E](),Map[E,Set[E]](),Map[(E,E),E](),Map[E,Set[E]](),Map[E,Set[E]](),new ArrayGraph())
  }
}