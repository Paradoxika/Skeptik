package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

abstract class DijkstraCon(
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]], 
    rN: Map[E,Set[E]], 
    g: WEqGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends Congruence(rep,cclass,lookup,lN,rN,g) {
  
  def explain(u: E, v: E): Option[EquationPath] = {
    g.explain(u, v)
  }
}

class FibCon (
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]],
    rN: Map[E,Set[E]],
    g: FibonacciGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends DijkstraCon(rep,cclass,lookup,lN,rN,g) {
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): Congruence = {
    if (g.isInstanceOf[FibonacciGraph]) 
      new FibCon(rep,cclass,lookup,lN,rN,g.asInstanceOf[FibonacciGraph])
    else
      this
  }
}

object FibCon {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new FibCon(Map[E,E](),Map[E,Set[E]](),Map[(E,E),E](),Map[E,Set[E]](),Map[E,Set[E]](),new FibonacciGraph())
  }
}

class ArrayCon (
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]],
    rN: Map[E,Set[E]],
    g: ArrayGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends DijkstraCon(rep,cclass,lookup,lN,rN,g) {
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): Congruence = {
    if (g.isInstanceOf[ArrayGraph]) 
      new ArrayCon(rep,cclass,lookup,lN,rN,g.asInstanceOf[ArrayGraph])
    else
      this
  }
}

object ArrayCon {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new ArrayCon(Map[E,E](),Map[E,Set[E]](),Map[(E,E),E](),Map[E,Set[E]](),Map[E,Set[E]](),new ArrayGraph())
  }
}