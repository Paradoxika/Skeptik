package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue

/**
 * Structure to store congruence closure terms in weighted graph
 */

abstract class CongruenceGraph(val lazyEdges: Map[(E,E),Option[EqW]], val order: Queue[(E,E)]) {
  
  def newGraph(edges: Map[(E,E),Option[EqW]], order: Queue[(E,E)]): CongruenceGraph
  
  def updateLazy: CongruenceGraph = {
    var ord = order
    var graph = this
    while (!ord.isEmpty) {
      val (currEl,currOrd) = ord.dequeue
      ord = currOrd
      graph = graph.updateLazyData(graph.lazyEdges,ord)
      graph = graph.addEdge(currEl._1, currEl._2, graph.lazyEdges.getOrElse((currEl),graph.lazyEdges(currEl.swap)))
    }
    graph
  }
  
  def updateLazyData(edges: Map[(E,E),Option[EqW]], order: Queue[(E,E)]): CongruenceGraph
  
  def lazyAddEdge(u: E, v: E, eq: Option[EqW]): CongruenceGraph = {
    val newQueue = if (!lazyEdges.isDefinedAt((u,v)) && !lazyEdges.isDefinedAt((v,u))) {
      order.enqueue((u,v))
    }
    else order
    eq match {
      case Some(_) => {
        newGraph(lazyEdges - ((u,v)) - ((v,u)) + ((u,v) -> eq),newQueue)
      }
      case None => if (lazyEdges.isDefinedAt((u,v)) || lazyEdges.isDefinedAt((v,u))) this else newGraph(lazyEdges +((u,v) -> eq),newQueue)
    }
  }
  
  def addEdge(u: E, v: E, eq: Option[EqW]): CongruenceGraph
  
  def explain(u: E, v: E)(implicit eqReferences: MMap[(E,E),EqW]): Option[EquationPath] 
  
  def subterms(term: E): Seq[E] = term match {
    case App(u,v) => {
      val x = uncurriedTerms(u) ++ uncurriedTerms(v)
      x
    }
    case _ => {
      Seq()
    }
  }
  
  def uncurriedTerms(term: E): Seq[E] = term.t match {
    case Arrow(_,_) => {
      term match {
        case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
        case _ => Seq()
      }
    }
    case _ => {
      Seq(term)
    }
  }
  
  def buildDD(t1: E, eq: Option[EqW], t2: E)(implicit eqReferences: MMap[(E,E),EqW]) = eq match {
    case None => {
      val (sub1,sub2) = (subterms(t1),subterms(t2))
      if (sub1.size != sub2.size) println("subterms don't match for " + (t1,t2) + " t: " + (t1.t,t2.t) + " s: " + (sub1,sub2) + "\n" + this)
      require(sub1.size == sub2.size)
      val explOpts = (sub1 zip sub2).toSet[Tuple2[E,E]].map(tuple => {
        
        val x = explain(tuple._1,tuple._2)
        x
      })
      val x = explOpts.filter(_.isDefined).map(_.get)
      x
    }
    case Some(e) => {
      Set[EquationPath]()
    }
  }
}