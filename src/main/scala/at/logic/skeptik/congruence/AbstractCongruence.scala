package at.logic.skeptik.congruence

import at.logic.skeptik.congruence.structure.{EqW,EquationPath,CongruenceGraph}
import at.logic.skeptik.expression.E

abstract class AbstractCongruence {
  def addEquality(eq: EqW): AbstractCongruence
  
  def addAll(eqs: Traversable[EqW]): AbstractCongruence
  
  def addNode(u: E): AbstractCongruence
  
  def explain(u: E, v: E): Option[EquationPath]
  
  def isCongruent(u: E, v: E): Boolean
  
  def g: CongruenceGraph
}