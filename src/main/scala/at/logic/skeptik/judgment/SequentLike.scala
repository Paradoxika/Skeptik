package at.logic.skeptik.judgment 


import at.logic.skeptik.expression.E
import at.logic.skeptik.util.unicode._
import at.logic.skeptik.util.rich.RichIterable._
import language.reflectiveCalls
import language.implicitConversions

/** A trait for sequent-like data structures.
 *
 *  @author  Bruno Woltzenlogel Paleo
 *  @version 0.2
 *  @since   0.2
 */
trait SequentLike[+Repr <: SequentLike[Repr]] {
  def ant: Iterable[E]
  def suc: Iterable[E]  
 
  def size = ant.size + suc.size + 1
  def logicalSize = ((ant ++ suc).map(_.logicalSize) :\ 0)(_ + _ + 1) 
 
  def isEmpty = ant.isEmpty || suc.isEmpty
  def antContains(f:E) = ant.contains(f)
  def sucContains(f:E) = suc.contains(f)
  def contains(f:E) = antContains(f) || sucContains(f)
  
  def subsequentOf(that: Sequent) = ant.forall(f => that.ant contains f) && suc.forall(f => that.suc contains f)
  
  def isTautological = ant.exists(f => suc contains f)
  
  def +(f:E): Repr
  def +:(f:E): Repr
  def -(f:E): Repr
  def -:(f:E): Repr
  
  def union(that: Sequent): Repr
  def diff(that: Sequent): Repr
  def intersect(that: Sequent): Repr
}
