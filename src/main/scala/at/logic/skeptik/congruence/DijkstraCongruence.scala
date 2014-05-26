package at.logic.skeptik.congruence

import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.congruence.Congruence

class FibonacciCongruence (
    eqReferences: MMap[(E,E),EqW] = MMap[(E,E),EqW](), 
    find: FindTable = new FindTable(), 
    deduced: Queue[(E,E)] = Queue[(E,E)](), 
    g: WEqGraph = new WEqGraph()) extends DijkstraCongruence(eqReferences,find,deduced,g) with earlyRes  {
  
  def newDijkstra: EquationDijkstra = {
    new FibonacciDijkstra(eqReferences)
  }
  def newCon(eqReferences: MMap[(E,E),EqW], find: FindTable, deduced: Queue[(E,E)], g: CongruenceGraph): Congruence = {
    if (g.isInstanceOf[WEqGraph])
      new FibonacciCongruence(eqReferences,find,deduced,g.asInstanceOf[WEqGraph])
    else
      this
  }
}

class ArrayCongruence (
    eqReferences: MMap[(E,E),EqW] = MMap[(E,E),EqW](), 
    find: FindTable = new FindTable(), 
    deduced: Queue[(E,E)] = Queue[(E,E)](), 
    g: WEqGraph = new WEqGraph()) extends DijkstraCongruence(eqReferences,find,deduced,g) with earlyRes {
  
  def newDijkstra: EquationDijkstra = {
    new ArrayDijkstra(eqReferences)
  }
  def newCon(eqReferences: MMap[(E,E),EqW], find: FindTable, deduced: Queue[(E,E)], g: CongruenceGraph): Congruence = {
    if (g.isInstanceOf[WEqGraph])
      new ArrayCongruence(eqReferences,find,deduced,g.asInstanceOf[WEqGraph])
    else
      this
  }
}

abstract class DijkstraCongruence (
    eqReferences: MMap[(E,E),EqW] = MMap[(E,E),EqW](), 
    find: FindTable = new FindTable(), 
    deduced: Queue[(E,E)] = Queue[(E,E)](), 
    g: WEqGraph = new WEqGraph()) extends Congruence(eqReferences,find,deduced,g) {
  
  def newDijkstra: EquationDijkstra
  
  def resolveDeduced(u: E, v: E): Congruence = {
    u match {
      case App(u1,u2) => {
        v match {
          case App(v1,v2) => {
            val path1 = 
              if (u1 == v1) new EquationPath(u1,None)
              else callDijkstra(u1,v1,g.graph)
            val path2 = 
              if (u2 == v2) new EquationPath(u2,None)
              else callDijkstra(u2,v2,g.graph)
            val eq1 = path1.originalEqs
            val eq2 = path2.originalEqs
            val eqAll = eq1 union eq2
           
            val weight = eqAll.size
            val x = EqW(u,v, eqReferences)
//            println((u1,v1) + " : " + path1)
//            println((u2,v2) + " : " + path2)
            val eqLabel = EqLabel(x,Some(path1,path2))
            updateGraph(g.addEdge(u, v, eqLabel, weight))
          }
          case _ => this
        }
      }
      case _ => this
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