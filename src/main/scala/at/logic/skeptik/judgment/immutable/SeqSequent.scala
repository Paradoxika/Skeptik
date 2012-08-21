package at.logic.skeptik.judgment
package immutable

import at.logic.skeptik.expression.E
  

class SeqSequent(val ant: Seq[E], val suc: Seq[E]) extends ASequent { 
  def +(f:E) = new SeqSequent(ant, suc :+ f)
  def +:(f:E) = new SeqSequent(ant :+ f, suc)
  def -(f:E) =  new SeqSequent(ant, suc.filterNot(_ == f))
  def -:(f:E) = new SeqSequent(ant.filterNot(_ == f), suc)
}

object SeqSequent {
  def apply() = new SeqSequent(Seq(),Seq())
  def apply(s: Sequent) = new SeqSequent(s.ant.toSeq, s.suc.toSeq)
}

