package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.algorithm.congruence.EqW

abstract class EqAxiom(override val mainFormulas: Sequent) extends SequentProofNode
  with Nullary with NoImplicitContraction {
  def getConclusionEq: E = {
    conclusion.suc.last
  }
}

class EqReflexive(override val mainFormulas: Sequent) extends EqAxiom(mainFormulas)

object EqReflexive {
  def apply(conclusion: Sequent) = new EqReflexive(conclusion)
  def apply(expr: E, eqReferences: MMap[(E,E),EqW]) = {
    expr match {
      case App(App(e,t1),t2) if (t1 == t2 && EqW.isEq(expr)) =>  new EqReflexive(new Sequent(Seq(),Seq(expr)))
      case _ => {
        if (expr.t == i) {
          val x = eqReferences.getOrElse((expr,expr), EqW(expr,expr)).equality
          if (x.toString == "((f2 c_5 c_2) = c_3)" || x.toString == "(c_3 = (f2 c_5 c_2))") println("creating " + x + " while creating EqReflexive node") 
          new EqReflexive(new Sequent(Seq(),Seq(x)))
        }
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
  
  def apply(eqsLeft: Seq[EqW], t1: E, t2: E, eqReferences: MMap[(E,E),EqW]) = { // Semantics not checked!
    new EqTransitive(new Sequent(eqsLeft.map(_.equality),Seq(EqW(t1,t2).equality)))
  }
  
  def apply(eq1: EqW, eq2: EqW, eqReferences: MMap[(E,E),EqW] = MMap[(E,E),EqW]()) = {
    val (u1,u2,v1,v2) = (eq1.l,eq1.r,eq2.l,eq2.r)
    val (t1,t2) = 
      if (u1 == v1) (u2,v2)
      else if (u1 == v2) (u2,v1)
      else if (u2 == v1) (u1,v2)
      else if (u2 == v2) (u1,v1)
      else throw new Exception("Error occured while creating EQtransitive node: "+ eq1 + " and " + eq2 + " don't form a transitivity chain")
    val x = EqW(t1,t2).equality
    new EqTransitive(new Sequent(Seq(eq1.equality,eq2.equality),Seq(x)))
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqTransitive => Some(p.conclusion)
    case _ => None
  }
}

class EqCongruent(override val mainFormulas: Sequent) extends EqAxiom(mainFormulas)

object EqCongruent {
  def apply(conclusion: Sequent) = new EqCongruent(conclusion)
  def apply(expl: EqW, eq: EqW) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(Seq(expl.equality),Seq(eq.equality)))
  }
  def apply(expl1: EqW, expl2: EqW, eq: EqW) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(Seq(expl1.equality,expl2.equality),Seq(eq.equality)))
  }
  def apply(expls: Seq[EqW], eq: EqW) = { //Semantics are not checked (yet)
    new EqCongruent(new Sequent(expls.map(_.equality),Seq(eq.equality)))
  }
  def unapply(p: SequentProofNode) = p match {
    case p: EqCongruent => Some(p.conclusion)
    case _ => None
  }
}