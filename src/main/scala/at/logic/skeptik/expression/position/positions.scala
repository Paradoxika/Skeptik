package at.logic.skeptik.expression
package position
  
class InexistentPositionException(e: E, position: Position) extends Exception("Position " + position + " does not exist in expression " + e)

abstract class Position {
  
  // returns the subformulas of f at these positions
  def !!:(e:E): Seq[E]
  
  // applies f at these positions in formula
  def @:(f: E => E)(e: E): E  

  def existsIn(e: E): Boolean = ! !!:(e).isEmpty
  
  def ||(that: Position) = new OrPosition(this, that)
  
  def *(that: Position) = new ComposedPosition(this, that)
  
  def toSinglePositions(e: E) = {
    val subs = !!:(e)
    for (i <- subs.indices) yield new IndexedPosition(new PredicatePosition(_ eq subs(i)), i)
  }
}

abstract class SinglePosition extends Position {
  def !:(e:E): Option[E]
  def !!:(e:E) = !:(e) match {
    case None => Seq()
    case Some(exp) => Seq(exp)
  }
  
  def getSubpositions(e: E):Seq[SinglePosition] = !:(e) match {
    case Some(sub) => for (p <- TotalPosition.toSinglePositions(sub)) yield (this * p).toSinglePositions(e)(0) 
    case None => Seq()
  }
}

class IndexedPosition(p: Position, index: Int) extends SinglePosition {
  def !:(e:E) = try { Some((e !!: p)(index)) } catch { case _ => None }
  
  def @:(f: E => E)(e: E) = !:(e) match {
    case Some(sub) => (f @: new PredicatePosition(_ eq sub))(e)
    case None => e
  }
}

class ComposedPosition(first: Position, second: Position) extends Position {
  def !!:(e:E) = (Seq(e) /: Seq(first,second)) {(s, p) => (for (e <- s) yield {e !!: p}).flatten}
  
  def @:(f: E => E)(e: E) = {
    val replacements = for (sub <- e !!: first) yield (sub, (f @: second)(sub))
    def g(sub: E) = replacements.find(_._1 eq sub).get._2 
    (g _ @: first)(e)
  } 
}
 
class OrPosition(left: Position, right: Position) extends Position {
  def !!:(e:E) = {
    val l = e !!: left; val r = e !!: right; 
    l ++ r.filterNot(e => l.exists(_ eq e))
  }
  
  def @:(f: E => E)(exp: E) = (f @: new PredicatePosition(e => !!:(exp).exists(_ eq e) ))(exp)
}

object EmptyPosition extends Position {
  def !!:(e: E) = Seq(e)
  def @:(f: E => E)(e:E) = f(e)
}

object TotalPosition extends PredicatePosition(_ => true)

class PredicatePosition(val isSearchedExpression: E => Boolean) extends Position {
  def !!:(expression:E) = {
    def rec(e: E): Seq[E] = {
      if (isSearchedExpression(e)) Seq(e)
      else e match {
        case v: Var => Seq()
        case App(g,a) => rec(g) ++ rec(a)
        case Abs(v,g) => rec(v) ++ rec(g)
      }
    } 
    rec(expression)
  }
  
  def @:(f: E => E)(expression:E): E = {
    def rec(e: E): E = {
      if (isSearchedExpression(e)) f(e)
      else e match {
        case v: Var => v
        case App(g,a) => App(rec(g),rec(a))
        case Abs(v,g) => Abs(rec(v).asInstanceOf[Var],rec(g))
      }     
    } 
    rec(expression)
  }
  
}