package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.PriorityQueue
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashSet => MSet}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.algorithm.congruence.EqW

class EquationDijkstra(references: MMap[(E,E),EqW]) extends Dijkstra[E,EqLabel](references) {
  
  def pi(u: E): EquationTree = {
    pathTrees.getOrElseUpdate(u,new EquationTree(u,None))
  }
  
  def setPi(u: E, l: EqLabel, v: E) = {
    val eqTreeEdge = new EqTreeEdge(pi(v),l)
    val p = new EquationTree(u,Some(eqTreeEdge))
    pathTrees.update(u, p)
  }
//  def isDiscounted(l: T2)
  
//  override def isDiscounted(l: EqLabel) {
//    true
//  }
}

abstract class Dijkstra[T1,T2](references: MMap[(E,E),EqW]) {
  
  val distances = MMap[T1,Int]()
  val pathTrees = MMap[T1,EquationTree]()
  val discount = MSet[EqW]()
  
  def d(u: T1) = {
    distances.getOrElse(u, Integer.MAX_VALUE)
  }
    
  def pi(u: T1): EquationTree 

  def setPi(u: T1, l: T2, v: T1)
  
  def isDiscounted(l: T2): Boolean = {
    if (l.isInstanceOf[EqLabel]) {
      val lEqL = l.asInstanceOf[EqLabel]
      val eq = lEqL._1
//      println("TRINGELINGEDINGDONG")
      discount.contains(eq)
    }
    else false
  }
  
  def apply(s: T1, target: T1, g: WGraph[T1,T2]): EquationTree = {
    if (s == target && s.isInstanceOf[E]) {
      val sE = s.asInstanceOf[E]
      val end = new EquationTree(sE,None)
      val x = EqW(sE,sE)
      if (x.toString == "((f2 c_5 c_2) = c_3)" || x.toString == "(c_3 = (f2 c_5 c_2))") println("creating " + x + " when shortest path between two equal expr is asked")
      val eqTreeEdge = new EqTreeEdge(end,(x,None))
      new EquationTree(sE,Some(eqTreeEdge))
    }
    else {
      this(s,g)
      pi(target)
    }
  }
  
  def apply(s: T1, gIn: WGraph[T1,T2]): Unit = {
    var g = gIn
    distances.clear
    pathTrees.clear
    discount.clear
    
    distances += (s -> 0)
    
//    val q = new PriorityQueue[T1]()(new distOrder)
    
    val q = new ArrayPQ[T1,Int]()
//    g.vertices.foreach(q.enqueue(_))
    
    g.vertices.foreach(v => q.insert(v, d(v)))
    
//    println("init q with call to " + s + ": " + q)
    
    def w(u: T1, l: T2, v: T1) = {
      val w1 = g.weights.getOrElse((u,l,v), Integer.MAX_VALUE)
//      println("checking " + (u,v) + " discounts: " + discount)
      if (isDiscounted(l)) {
//        println((u,v) + " are discounted")
        w1 - 1
      }
      else w1
    }
    
    def relax(u: T1, l: T2, v: T1) = {
//      println("relax " + (u,v) + " is discounted? " + isDiscounted(l))
      val y = d(u).toLong + w(u,l,v).toLong
      val x = if (y >= Integer.MAX_VALUE) Integer.MAX_VALUE else y.toInt //Note that d(u) and w(u,v) are always positive
//      println("d(" + v +"): " + d(v) + " >? " + "d("+u+"):"+d(u)+" + w("+u+","+v+"): "+w(u,v) + " = " + x)
      if (d(v) > x) {
        distances.update(v, x)
        setPi(v,l,u)
        q.decreaseKey(v, x)
      }
    }
    
    while(!q.isEmpty) {
      
//      val u = q.dequeue
//      println("q before " + q + " when starting with " + s)
      val u = q.extractMin
//      println("process " + u + " which distance is: " + d(u))
      
      val l = pi(u).allEqs
      l.foreach(lE => {
//        println("discounting " + lE)
        discount += lE
      })
      
      val adj = g.adjacent.getOrElse(u, List())
//      println("adjacent of " + u + " is " + adj)
//      println("q before: " + q.map(el => el + " -> " + d(el)).mkString(",") )
      adj.foreach(x => {
        relax(u,x._1,x._2)
//        println(x._2 + " new distance: " + d(x._2))
//        q.
      })
//      println("q after: " + q.map(el => el + " -> " + d(el)).mkString(",") )
    }
  }  
  
  class distOrder extends Ordering[T1] {
      override def compare(a: T1, b: T1) = - (d(a) compare d(b))
    }
}