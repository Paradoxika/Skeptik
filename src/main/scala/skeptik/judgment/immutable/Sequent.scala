package skeptik.judgment
package immutable

import skeptik.expression.E
import skeptik.util.unicode._
  

class SetSequent(val ant: Set[E], val suc: Set[E]) extends ASequent { 
  def +(f:E) = new SetSequent(ant, suc + f)
  def +:(f:E) = new SetSequent(ant + f, suc)
  def -(f:E) =  new SetSequent(ant, suc - f)
  def -:(f:E) = new SetSequent(ant - f, suc)
  
  def +(e: Either[E,E]): SetSequent = e match {
    case Left(f) => +:(f)
    case Right(f) => this.+(f)
  }  
}



