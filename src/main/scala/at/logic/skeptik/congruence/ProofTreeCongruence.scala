package at.logic.skeptik.congruence

import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.expression.E
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import at.logic.skeptik.algorithm.dijkstra.EquationPath
import at.logic.skeptik.congruence.structure._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashMap => MMap}

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
  
  def resolveEarly = true
  
  def addEdge(u: E, v: E, eq: EqW): Congruence = {
    val newG = g.addEdge(u, v, Some(eq))
    updateGraph(newG)
  }

  def resolveDeduced(u: E, v: E): Congruence = {
    val newG = g.addEdge(u, v, None)
    updateGraph(newG)
  }
  
  def explain(u: E, v: E): Option[EquationPath] = {
    g.explain(u,v,eqReferences)
  }
}