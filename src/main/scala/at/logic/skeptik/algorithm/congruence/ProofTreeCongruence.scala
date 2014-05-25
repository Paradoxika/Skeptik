package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.E
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import at.logic.skeptik.algorithm.dijkstra.EquationPath

class ProofTreeCongruence(
    eqReferences: MMap[(E,E),EqW] = MMap[(E,E),EqW](), 
    find: FindTable = new FindTable(), 
    deduced: Queue[(E,E)] = Queue[(E,E)](), 
    g: ProofForest = ProofForest()) extends Congruence(eqReferences,find,deduced,g) {
  
  def newCon(eqReferences: MMap[(E,E),EqW], find: FindTable, deduced: Queue[(E,E)], g: CongruenceGraph): Congruence = {
    if (g.isInstanceOf[ProofForest]) {
      new ProofTreeCongruence(eqReferences,find,deduced,g.asInstanceOf[ProofForest])
    }
    else this
  }
  
  def resolveEarly = false
  
  def addEdgeEarly(u: E, v: E, eq: EqW): Congruence = {
    this
  }

  def addEdgeLate(u: E, v: E, eq: EqW): Congruence = {
    val newG = g.addEdge(u, v, Some(eq))
    updateGraph(newG)
  }
  
  def resolveDeduced(u: E, v: E): Congruence = {
    this
  }
  
  def explain(u: E, v: E): Option[EquationPath] = {
    None
  }
}