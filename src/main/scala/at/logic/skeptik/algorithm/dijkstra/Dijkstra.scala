package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.PriorityQueue

class Dijkstra[T1,T2] {

  val distances = MMap[T1,Int]()
  val pathTrees = MMap[T1,PathTree[T1,T2]]()
  
  def d(u: T1) = {
    distances.getOrElse(u, Integer.MAX_VALUE)
  }
    
  def pi(u: T1) = {
    pathTrees.getOrElseUpdate(u,new PathTree(u,None))
  }
  
  def setPi(u: T1, l: Set[T2], v: T1) = {
    pathTrees.update(u, new PathTree(u,Some(pi(v),l)))
  }
  
  def apply(g: WGraph[T1,Set[T2]], s: T1, tabu: List[(T1,T2,T1)]): Unit = {
    distances.clear
    pathTrees.clear
    
    distances += (s -> 0)
    
//    val q = new PriorityQueue[T1]()(new distOrder)
    
    val q = new ArrayPQ[T1,Int]()
    
//    g.vertices.foreach(q.enqueue(_))
    
    g.vertices.foreach(v => q.insert(v, d(v)))
    
    def w(u: T1, l: Set[T2], v: T1) = {
      if (tabu.contains(u,v)) Integer.MAX_VALUE
      else g.weights.getOrElse((u,l,v), Integer.MAX_VALUE)
    }
    
    def relax(u: T1, l: Set[T2], v: T1) = {
      val y = d(u) + w(u,l,v)
      val x = if (y < 0) Integer.MAX_VALUE else y //Note that d(u) and w(u,v) are always positive
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
      
//      println("q before: " + q.map(el => el + " -> " + d(el)).mkString(",") )
      g.adjacent.getOrElse(u, List()).foreach(x => {
        relax(u,x._1,x._2)
//        println(x._2 + " new distance: " + d(x._2))
//        q.
      })
//      println("q after: " + q.map(el => el + " -> " + d(el)).mkString(",") )
    }
  }
  
    def apply(g: WGraph[T1,Set[T2]], s: T1, tabu: List[(T1,T2,T1)], target: T1): PathTree[T1,T2] = {
      this(g,s,tabu)
      pi(target)
    }
    
    def apply(u: T1, v: T1, g: WGraph[T1,Set[T2]]): PathTree[T1,T2] = {
      this(g,u,List(),v)
    }
  
  class distOrder extends Ordering[T1] {
      override def compare(a: T1, b: T1) = - (d(a) compare d(b))
    }
}