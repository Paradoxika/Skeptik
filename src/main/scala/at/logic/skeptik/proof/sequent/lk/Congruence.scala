package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._

abstract class EqAxiom(override val mainFormulas: Sequent) extends Axiom(mainFormulas) {
  def getConclusionEq: E = {
    conclusion.suc.last
  }
}

class EqReflexive(override val mainFormulas: Sequent) extends EqAxiom(mainFormulas)

object EqReflexive {
  def apply(conclusion: Sequent) = new EqReflexive(conclusion)
  def apply(expr: E) = {
    expr match {
      case App(App(e,t1),t2) if (t1 == t2 && Eq.?:(expr)) =>  new EqReflexive(new Sequent(Seq(),Seq(expr)))
      case _ => {
        if (expr.t == i) new EqReflexive(new Sequent(Seq(),Seq(Eq(expr,expr))))
        else throw new Exception("Error occured while creating EQReflexive node: "+ expr + " neither is an instance of reflexivity nor a term")
//        println(expr + " type: " + expr.t)
//        new EqReflexive(new Sequent(Seq(),Seq(Eq(expr,expr))))
      }
    }
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqReflexive => Some(p.conclusion)
    case _ => None
  }
}

class EqTransitive(override val mainFormulas: Sequent) extends EqAxiom(mainFormulas)

object EqTransitive {
  def apply(conclusion: Sequent) = new EqTransitive(conclusion)
  def apply(eq1: E, eq2: E) = {
    eq1 match {
      case App(App(e,u1),u2) if (Eq.?:(eq1)) => eq2 match {
        case App(App(e,v1),v2) if (Eq.?:(eq2)) => {
          val (t1,t2) =
            if (u1 == v1) (u2,v2)
            else if (u1 == v2) (u2,v1)
            else if (u2 == v1) (u1,v2)
            else if (u2 == v2) (u1,v1)
            else throw new Exception("Error occured while creating EQtransitive node: "+ eq1 + " and " + eq2 + " don't form a transitivity chain")
          new EqTransitive(new Sequent(Seq(eq1,eq2),Seq(Eq(t1,t2))))
        } 
      }  
    }
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqTransitive => Some(p.conclusion)
    case _ => None
  }
}

class EqCongruent(override val mainFormulas: Sequent) extends EqAxiom(mainFormulas)

object EqCongruent {
  def apply(conclusion: Sequent) = new EqCongruent(conclusion)
  def apply(expl: E, eq: E) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(Seq(expl),Seq(eq)))
  }
  def apply(expl1: E, expl2: E, eq: E) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(Seq(expl1,expl2),Seq(eq)))
  }
  def apply(expls: Seq[E], eq: E) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(expls,Seq(eq)))
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqCongruent => Some(p.conclusion)
    case _ => None
  }
}

//class Axiom(override val mainFormulas: Sequent) extends SequentProofNode
//with Nullary with NoImplicitContraction
//
//object Axiom {
//  def apply(conclusion: Sequent) = new Axiom(conclusion)
//  def unapply(p: SequentProofNode) = p match {
//    case p: Axiom => Some(p.conclusion)
//    case _ => None
//  }
//}