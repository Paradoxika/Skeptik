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
    u match {
      case App(u1,u2) => {
        v match {
          case App(v1,v2) => {
            print(u1 + " t: " + u1.t+ " ")
            print(v1 + " t: " + v1.t+ " ")
            print(u2 + " t: " + u2.t +" ")
            print(v2 + " t: " + v2.t +"\n")
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
            val x = EqW(u,v)
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