package at.logic.skeptik.expression
package formula

import at.logic.skeptik.expression.position.{Position,PredicatePosition}

abstract class Formula {
  def unapply(f:E):Option[_]
  def ?:(f: E) = unapply(f).isInstanceOf[Some[_]]
}

abstract class BinaryFormula(connective: Var) extends Formula {
  def apply(f1: E, f2: E) = App(App(connective,f1),f2)
  def unapply(e:E) = e match {
    case App(App(c,f1),f2) if c == connective => Some((f1,f2))
    case _ => None
  }  
}

abstract class UnaryFormula(connective: Var) extends Formula {
  def apply(f: E) = App(connective,f)
  def unapply(e:E) = e match {
    case App(c,f) if c == connective => Some(f)
    case _ => None
  }  
}

abstract class QuantifierFormula(quantifierC:T=>E) extends Formula {
  def apply(v:Var, f:E) = App(quantifierC(v.t), Abs(v,f))
  def apply(f:E, v:Var, p:Position) = {
    val h = (( (_:E) => v.copy) @: p)(f)
    App(quantifierC(v.t), Abs(v,h))
  }
  def apply(f:E, v:Var, t:E): E = apply(f, v, new PredicatePosition(_ == t)) 
    
  def unapply(e:E) = e match {
    case App(q, Abs(v,f)) if q == quantifierC(v.t) => Some((v,f))
    case _ => None
  }  
}


object Neg extends UnaryFormula(negC)

object And extends BinaryFormula(andC)

object Or extends BinaryFormula(orC)

object Imp extends BinaryFormula(impC)

object Eq {
//  def apply(term1: E, term2: E): App = {
//    require(term1.t == term2.t)
//    val t1Type = term1.t
//    new Equation(t1Type)(term1,term2)
//  }
  /**
   * called in: 
   * PathTree line 59
   * package at.logic.skeptik.proof.sequent.lk.congruence line 27 (EQReflexive), line 57 (EQTransitive)
   * Dijkstra line 55 (only reflexive eq)
   * 
   */
  def apply(term1: E, term2: E, eqReferences: scala.collection.mutable.HashMap[(E,E),App]): App = {
    require(term1.t == term2.t)
//    val istherestill = eqReferences.values.find(p => {(p.toString == "((f1 c_3 c_3) = (f1 (f3 c6) (f3 c7)))" || p.toString == "((f1 (f3 c6) (f3 c7)) = (f1 c_3 c_3))") })
//    println("is there still?: " + istherestill + " ~ " + eqReferences.size)
    val thisOne= 
      ((term1.toString == "(f1 (f3 c_4) c_4)" && term2.toString == "(f1 (f2 c_4 c_4) (f2 c_4 c_4)))") 
        || ((term2.toString == "(f1 (f3 c_4) c_4)" && term1.toString == "(f1 (f2 c_4 c_4) (f2 c_4 c_4)))")))
    eqReferences.get((term1,term2)) match {
      case Some(eq) => {
        if (thisOne) println("found eq for " + (term1,term2))
        eq
      }
      case None => {
	    eqReferences.get((term2,term1)) match {
	      case Some(eq2) => {
	        if (thisOne) println("found eq for " + (term2,term1))
	        eq2
	      }
	      case None => {
	        if (thisOne) println("creating eq for " + (term1,term2))
//	        val y = Eq(term1,term2)
	        val y = new Equation(term1.t)(term1,term2)
	        val doPrint = (y.toString == "((f1 c_3 c_3) = (f1 (f3 c6) (f3 c7)))" || y.toString == "((f1 (f3 c6) (f3 c7)) = (f1 c_3 c_3))") 
	        if (doPrint) println("eqRef before adding " + y + " : " + eqReferences)
	        eqReferences += ((term1,term2) -> y)
	        eqReferences += ((term2,term1) -> y)
//	        eqReferences.update((term2,term1), y)
	        if (doPrint) println("eqRef before after " + y + " : " + eqReferences)
	        if (doPrint) println("Have to create " + y + " myself in Eq, apply (formulas)")
	        if (doPrint) println("eqs: " + eqReferences.values.mkString(","))
	        if (y.toString == "((f1 c_0 c_0) = (f1 c_0 (f2 c_0 c_0)))") println("CREATING THE ONE EQUATION IN EQ()")
	        if (y.toString == "((f1 c_0 (f2 c_0 c_0)) = (f1 c_0 c_0))") println("CREATING THE OTHER EQUATION IN EQ()")
	        y
	      }
	    }
	  }
    }
  }
//  def eqEquals(t1: E, t2: E): Boolean = {
//    if (Eq.?:(t1) && Eq.?:(t2)) {
//      val (u1,u2) = t1 match {
//        case App(App(c,f1),f2) => (f1,f2)
//      }
//      val (v1,v2) = t2 match {
//        case App(App(c,f1),f2) => (f1,f2)
//      }
//      ((u1 == v1) && (u2 == v2) || (u1 == v2) && (u2 == v1))
//    }
//    else t1 == t2
//  }
  def ?:(f: E) = { // very hacky!
    f match {
      case App(App(v,_),_) => v.toString == "="
      case _ => false
    }
  }
  def unapply(e:E) = e match {
    case App(q, Abs(v,f)) if v.toString == "=" => Some((v,f))
    case _ => None
  }  
}
  
object All extends QuantifierFormula(allC)  

object Ex extends QuantifierFormula(exC)

class Equation(t: T) extends BinaryFormula(eqC(t))

object Atom extends Formula {
  def apply(p: E, args: List[E]) = {
    val atom = AppRec(p,args)
    require(atom.t == o)
    atom
  }
  def unapply(e:E) = e match {
    case AppRec(f,args) if (e.t == o && !isLogicalConnective(f)) => Some((f,args))
    case _ => None
  }
}

