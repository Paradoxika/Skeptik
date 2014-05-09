package at.logic.skeptik.algorithm

import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.congruence.EqW

package object dijkstra {
//  type EqTreeEdge = Option[(EquationTree,(EqW,Option[(EquationTree,EquationTree)]))]
  type EqLabel = (EqW,Option[(EquationTree,EquationTree)])
}