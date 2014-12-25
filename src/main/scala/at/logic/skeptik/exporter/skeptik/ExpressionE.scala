package at.logic.skeptik.exporter
package skeptik

import at.logic.skeptik.expression.{E,Var,Abs,App,AppRec}
import at.logic.skeptik.expression.formula._

trait ExpressionE extends Exporter {
  def write(e: E): Unit = write(e.toString)
}