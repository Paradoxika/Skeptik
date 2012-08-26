package at.logic.skeptik.judgment 

import at.logic.skeptik.util.unicode._


/** An abstract superclass for all kinds of sequents.
 *
 *  @author  Bruno Woltzenlogel Paleo
 *  @version 0.2
 *  @since   0.2
 */
abstract class Sequent extends Judgment with SequentLike[Sequent] {

  def toSetSequent = new immutable.SetSequent(ant.toSet, suc.toSet)
  def toSeqSequent = new immutable.SeqSequent(ant.toSeq, suc.toSeq)
  
  override def equals(v: Any) = v match {    
      case that: Sequent => (that canEqual this) && (ant == that.ant) && (suc == that.suc) 
      case _ => false   
  }   
  def canEqual(other: Any) = other.isInstanceOf[Sequent]  
  override def hashCode = 42*ant.hashCode + suc.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
}