package at.logic.skeptik.exporter
package skeptik

import at.logic.skeptik.judgment.Sequent

trait SequentE extends ExpressionE {
  def write(s: Sequent): Unit = write(s.toString)
}