package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk._

/**
 * class EqW stands for equality wrapper
 * provides access methods l,r for the terms on the left and right side resp.
 * 
 * overrides equals to make EqW objects representing symmetric equal
 * which was the initial intention of creating this class in the first place
 * however literals are judgements, therefore EqW can't be a literal (yet?)
 * so this does not really solve the problem
 * 
 * reverse method is to get an EqW object representing r = l if the current equality is l = r
 */

class EqW(val equality :E) {
  
  def reverse = {
    val eqVar = new Var("=", (l.t -> (l.t -> o))) with Infix
    EqW(App(App(eqVar,r),l))
  }
  
  def l = equality match {
    case App(App(c,u),v) if c.toString == "=" => u
    case _ => throw new Exception("eq in Equation is not an equality")
  }
  
  def r = equality match {
    case App(App(c,u),v) if c.toString == "=" => v
    case _ => throw new Exception("eq in Equation is not an equality")
  }
  
  override def equals(other: Any) = {
    val res = other match {
      case that: EqW => {
        ((this.l == that.l) && (this.r == that.r) || (this.l == that.r) && (this.r == that.l))
      }
      case _ => false
    }
//    println("checking " + this + " == " + other + " ?: " + res)
    res
  }
  
  override def toString = equality.toString
}

/**
 * companion object of class EqW
 * 
 * the important methods are the isEq method, returning true iff the input expression is an equality
 * and the apply and unapply methods
 * 
 * the apply method with one argument checks whether the input expression is an equality and 
 * returns a respective EqW object in this case
 * 
 * the apply method with two arguments creates an equality between the terms
 * 
 * the resolve and resolveSymm methods are experiments to have special cases of the 
 * R.apply method for equalities, taking into account symmetry.
 * This is however not a very satisfactory solution and so far it does also not work properly
 */

object EqW {
  
  def resolveSymm (premise1:N, premise2:N) = {
    def findPivots(p1:N, p2:N): Option[(E,E)] = {
      for (auxL <- p1.conclusion.suc; auxR <- p2.conclusion.ant) if (auxL == auxR) return Some(auxL,auxR)
      return None
    }
    findPivots(premise1,premise2) match {
      case Some((auxL,auxR)) => {
        resolve(premise1,premise2,auxL)
      }
      case None => findPivots(premise2,premise1) match {
        case Some((auxL,auxR)) => resolve(premise2,premise1,auxL)
        case None => {
//          println("Not resolvable:")
//          println(premise1 + " class: " + premise1.getClass)
//          println(Proof(premise1))
//          println(premise2 + " class: " + premise2.getClass)
          throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
        }
      }
    }
  }
  
  def resolve(leftPremise: N, rightPremise: N, pivot: E) = {
    (leftPremise.conclusion.suc.find(EqW(_) == pivot), rightPremise.conclusion.ant.find(EqW(_) == pivot)) match {
      case (Some(auxL), Some(auxR)) => new R(leftPremise, rightPremise, auxL, auxR)
      case (None, None) => {
        (leftPremise.conclusion.suc.find(EqW(_).reverse.equality == pivot), rightPremise.conclusion.ant.find(EqW(_) == pivot)) match {
          case (Some(auxL), Some(auxR)) => new R(leftPremise, rightPremise, EqW(auxL).reverse.equality, auxR)
          case (None,None) => (leftPremise.conclusion.ant.find(EqW(_) == pivot), rightPremise.conclusion.suc.find(EqW(_) == pivot)) match {
            case (Some(auxL), Some(auxR)) => new R(rightPremise, leftPremise, auxR, auxL)
            case (None,None) => (leftPremise.conclusion.ant.find(EqW(_).reverse.equality == pivot), rightPremise.conclusion.suc.find(EqW(_) == pivot)) match {
              case (Some(auxL),Some(auxR)) => new R(rightPremise, leftPremise, auxR, EqW(auxL).reverse.equality)
              case _ => throw new Exception("Auxiliary formulas not found.\n"+leftPremise.conclusion + "\n" + rightPremise.conclusion + "\n" + pivot)
            }
          }
        }
      }
      case _ => throw new Exception("Auxiliary formulas not found.\n"+leftPremise.conclusion + "\n" + rightPremise.conclusion + "\n" + pivot)
    }
  } 
  
  def isEq(f: E) = {
    f match {
      case App(App(v,_),_) => v.toString == "="
      case _ => false
    }
  }
  
  def apply(t1: E, t2: E): EqW = {
    require(t1.t == t2.t)
    val eqVar = new Var("=", (t1.t -> (t1.t -> o))) with Infix
    new EqW(App(App(eqVar,t1),t2))
  }
    
  def apply(eq: E): EqW = {
    if (isEq(eq)) new EqW(eq)
    else throw new Exception("eq in Equation is not an equality")
  }
  
  def unapply(e:E) = e match {
    case App(App(c,u),v) if c.toString == "=" => Some((u,v))
    case _ => None
  } 
}