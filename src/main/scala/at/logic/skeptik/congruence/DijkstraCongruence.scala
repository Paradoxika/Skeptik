package at.logic.skeptik.congruence

import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.expression._
import scala.collection.immutable.Queue
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashMap => MMap}

class FibonacciCongruence (
    find: FindTable, 
    deduced: Queue[(E,E)], 
    g: WEqGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends DijkstraCongruence(find,deduced,g) with earlyRes  {
  
  def newDijkstra: EquationDijkstra = {
    new FibonacciDijkstra
  }
  def newCon(find: FindTable, deduced: Queue[(E,E)], g: CongruenceGraph)(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    if (g.isInstanceOf[WEqGraph])
      new FibonacciCongruence(find,deduced,g.asInstanceOf[WEqGraph])
    else
      this
  }
}

object FibonacciCongruence {
  
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new FibonacciCongruence(new FindTable(),Queue[(E,E)](),new FibonacciGraph)
  }
  
}

class ArrayCongruence ( 
    find: FindTable, 
    deduced: Queue[(E,E)], 
    g: WEqGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends DijkstraCongruence(find,deduced,g) with earlyRes {
  
  def newDijkstra: EquationDijkstra = {
    new ArrayDijkstra
  }
  def newCon(find: FindTable, deduced: Queue[(E,E)], g: CongruenceGraph)(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    if (g.isInstanceOf[WEqGraph])
      new ArrayCongruence(find,deduced,g.asInstanceOf[WEqGraph])
    else
      this
  }
}

abstract class DijkstraCongruence (
    find: FindTable = new FindTable(), 
    deduced: Queue[(E,E)] = Queue[(E,E)](), 
    g: WEqGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends Congruence(find,deduced,g) {
  
  def newDijkstra: EquationDijkstra
  
  def resolveDeduced(u: E, v: E): Congruence = {
    val paths = buildDD(u,None,v)
    val eqAll = paths.foldLeft(Set[EqW]())({(A,B) => 
      A union B.originalEqs
    })
    val weight = eqAll.size
    val eqLabel = EqLabel(EqW(u,v),paths)
    updateGraph(g.addEdge(u, v, eqLabel, weight))
  }
    
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
  
  def callDijkstra(u: E, v: E, g: WGraph[E,EqLabel]) ={
    val dij = newDijkstra
    dij(u,v,g)
  }

  
  def explain(u: E, v: E): Option[EquationPath] = {
    if (!resolveEarly) resolveDeducedQueue 
    val dij = newDijkstra
    val path = dij(u,v,g.graph)
    if (path.isEmpty) None else Some(path)
  }
}