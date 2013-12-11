package at.logic.skeptik.exporter

import at.logic.skeptik.expression.E
import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}

import java.io.Writer



abstract class Exporter extends Writer {
  def write(e: E)
  def write(s: Sequent)
  def write(p: Proof[N])
}
