package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

abstract class CongruenceGraph {
  
  def addEdge(u: E, v: E, eq: Option[EqW]): CongruenceGraph
  
  def explain(u: E, v: E)(implicit eqReferences: MMap[(E,E),EqW]): Option[EquationPath] 
  
  def subterms(term: E): Seq[E] = term match {
    case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
    case _ => Seq()
  }
  
  def uncurriedTerms(term: E): Seq[E] = term.t match {
    case Arrow(_,_) => {
      term match {
        case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
        case _ => Seq()
      }
    }
    case _ => Seq(term)
  }
  
  def buildDD(t1: E, eq: Option[EqW], t2: E)(implicit eqReferences: MMap[(E,E),EqW]) = eq match {
    case None => {
      val (sub1,sub2) = (subterms(t1),subterms(t2))
      require(sub1.size == sub2.size)
      val explOpts = (sub1 zip sub2).map(tuple => explain(tuple._1,tuple._2))
      explOpts.filter(_.isDefined).map(_.get).toSet
    }
    case Some(_) => {
//        println("skipping deduce trees!")
      Set[EquationPath]()
    }
  }
}