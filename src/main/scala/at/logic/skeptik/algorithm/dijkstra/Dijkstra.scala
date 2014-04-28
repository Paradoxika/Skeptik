package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.PriorityQueue
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashSet => MSet}

class EquationDijkstra extends Dijkstra[E,EqLabel] {
  
  def pi(u: E): EquationTree = {
    pathTrees.getOrElseUpdate(u,new EquationTree(u,None))
  }
  
  def setPi(u: E, l: EqLabel, v: E) = {
    val p = new EquationTree(u,Some(pi(v),l))
    pathTrees.update(u, new EquationTree(u,Some(pi(v),l)))
  }
}

abstract class Dijkstra[T1,T2] {
  
  val distances = MMap[T1,Int]()
  val pathTrees = MMap[T1,EquationTree]()
  
  def d(u: T1) = {
    distances.getOrElse(u, Integer.MAX_VALUE)
  }
    
  def pi(u: T1): EquationTree //= {
//    pathTrees.getOrElseUpdate(u,new EquationTree(u,None))
//  }
  
  def setPi(u: T1, l: T2, v: T1)// = {
//    val p = new SelfPathTree(u,Some(pi(v),l))
//    pathTrees.update(u, new SelfPathTree(u,Some(pi(v)),l))))
//  }
  
  def apply(s: T1, gIn: WGraph[T1,T2]): Unit = {
    var g = gIn
    distances.clear
    pathTrees.clear
    val discount = MSet[(E,E)]()
    
    distances += (s -> 0)
    
//    val q = new PriorityQueue[T1]()(new distOrder)
    
    val q = new ArrayPQ[T1,Int]()
//    g.vertices.foreach(q.enqueue(_))
    
    g.vertices.foreach(v => q.insert(v, d(v)))
    
//    println("init q with call to " + s + ": " + q)
    
    def w(u: T1, l: T2, v: T1) = {
      val w1 = g.weights.getOrElse((u,l,v), Integer.MAX_VALUE)
//      println("checking " + (u,v) + " discounts: " + discount)
      if (u.isInstanceOf[E] && v.isInstanceOf[E]) {
        val uE = u.asInstanceOf[E]
        val vE = v.asInstanceOf[E]
        if (discount.contains((uE,vE)) || discount.contains((vE,uE))) {
//          println((u,v) + " are discounted")
          w1 - 1
        }
        else w1
      }
      else w1
//      if (tabu.contains(u,v)) Integer.MAX_VALUE
//      else g.weights.getOrElse((u,l,v), Integer.MAX_VALUE)
    }
    
    def relax(u: T1, l: T2, v: T1) = {
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
//      println("q before " + q)
      val u = q.extractMin
//      println("process " + u + " which distance is: " + d(u))
      
//      val l = pi(u).lastLabel
//      doDiscounts(l)
      
//      println("q before: " + q.map(el => el + " -> " + d(el)).mkString(",") )
      g.adjacent.getOrElse(u, List()).foreach(x => {
        relax(u,x._1,x._2)
//        println(x._2 + " new distance: " + d(x._2))
//        q.
      })
//      println("q after: " + q.map(el => el + " -> " + d(el)).mkString(",") )
    }
    
//    def doDiscounts(l: Set[T2]) {
//      l.foreach(label => {
//          if (label.isInstanceOf[App]){
//            val lApp = label.asInstanceOf[App]
//            val f = lApp.function
//            if (f.isInstanceOf[App]) {
//              val fApp = f.asInstanceOf[App]
////              println("discounting: " + (fApp.argument,lApp.argument))
//              g = g.addUndirectedEdge((fApp.argument.asInstanceOf[T1],Set(), lApp.argument.asInstanceOf[T1]),0)
////              discount += ((fApp.argument,lApp.argument))
//            }
//          }
//        })
//    }
  }
  
    def apply(s: T1, target: T1, g: WGraph[T1,T2]): EquationTree = {
      this(s,g)
      pi(target)
    }
    
//    def apply(u: T1, v: T1, g: WGraph[T1,Set[T2]]): PathTree[T1,T2] = {
//      this(g,u,v)
//    }
  
  class distOrder extends Ordering[T1] {
      override def compare(a: T1, b: T1) = - (d(a) compare d(b))
    }
}