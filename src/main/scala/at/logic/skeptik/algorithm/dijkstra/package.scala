package at.logic.skeptik.algorithm

//import at.logic.skeptik.expression.{App => PApp}
import at.logic.skeptik.expression._

package object dijkstra {
  type EqTreeEdge = Option[(EquationTree,(App,Option[(EquationTree,EquationTree)]))]
  type EqLabel = (App,Option[(EquationTree,EquationTree)])
}