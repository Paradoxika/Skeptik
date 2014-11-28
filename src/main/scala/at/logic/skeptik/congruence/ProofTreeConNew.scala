package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

class ProofTreeCon(
    rep: Map[E,E], 
    cclass: Map[E,Set[E]], 
    lookup: Map[(E,E),E], 
    lN: Map[E,Set[E]], 
    rN: Map[E,Set[E]], 
    g: ProofForest)
    (implicit eqReferences: MMap[(E,E),EqW]) extends Congruence(rep,cclass,lookup,lN,rN,g) {

  def explain(u: E, v: E): Option[EquationPath] = {
    g.explain(u,v)
  }
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): Congruence = {
    if (g.isInstanceOf[ProofForest]) 
      new ProofTreeCon(rep,cclass,lookup,lN,rN,g.asInstanceOf[ProofForest])
    else
      this
  }
}

object ProofTreeCon {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new ProofTreeCon(Map[E,E](),Map[E,Set[E]](),Map[(E,E),E](),Map[E,Set[E]](),Map[E,Set[E]](),new ProofForest())
  }
}