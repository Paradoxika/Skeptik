package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression.E

abstract class CongruenceGraph {
  
  def addEdge(u: E, v: E, eq: Option[EqW]): CongruenceGraph
  
}