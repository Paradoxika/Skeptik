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
    new ArrayCongruence(new FindTable(), Queue[(E,E)](), new ArrayGraph)
  }
}

trait FibonacciStructure {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    new FibonacciCongruence(new FindTable(), Queue[(E,E)](), new FibonacciGraph)
  }
}

trait ProofTreeStructure {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    new ProofTreeCongruence(new FindTable(), Queue[(E,E)](), ProofForest())
  }
}

trait ArrayStructureNew {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): CongruenceNew = {
    ArrayConNew(eqReferences)
  }
}

trait FibonacciStructureNew {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): CongruenceNew = {
    FibConNew(eqReferences)
  }
}

trait ProofTreeStructureNew {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): CongruenceNew = {
    ProofTreeConNew(eqReferences)
  }
}