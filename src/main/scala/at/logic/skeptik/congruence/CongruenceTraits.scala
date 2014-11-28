package at.logic.skeptik.congruence

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import at.logic.skeptik.congruence._
import at.logic.skeptik.congruence.structure.EqW
import at.logic.skeptik.expression.E
import at.logic.skeptik.congruence.structure._

trait earlyRes {
  def resolveEarly: Boolean = true
}

trait lazyRes {
  def resolveEarly: Boolean = false
}

trait ArrayStructure {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    ArrayCon(eqReferences)
  }
}

trait FibonacciStructure {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    FibCon(eqReferences)
  }
}

trait ProofTreeStructure {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    ProofTreeCon(eqReferences)
  }
}