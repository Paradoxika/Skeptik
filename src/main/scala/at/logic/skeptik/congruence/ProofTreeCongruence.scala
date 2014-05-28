package at.logic.skeptik.congruence

import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.expression.E
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import at.logic.skeptik.congruence.structure.EquationPath
import at.logic.skeptik.congruence.structure._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashMap => MMap}

class ProofTreeCongruence(
    find: FindTable = new FindTable(), 
    deduced: Queue[(E,E)] = Queue[(E,E)](), 
    g: ProofForest = ProofForest())
    (implicit eqReferences: MMap[(E,E),EqW]) extends Congruence(find,deduced,g) {
  
  def newCon(find: FindTable, deduced: Queue[(E,E)], g: CongruenceGraph)(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    if (g.isInstanceOf[ProofForest]) {
      new ProofTreeCongruence(find,deduced,g.asInstanceOf[ProofForest])
    }
    else this
  }
  
  def resolveEarly = true

  def resolveDeduced(u: E, v: E): Congruence = {
    val newG = g.addEdge(u, v, None)
    updateGraph(newG)
  }
  
  def explain(u: E, v: E): Option[EquationPath] = {
    g.explain(u,v)
  }
}