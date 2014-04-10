package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.algorithm.dijkstra._
import scala.collection.mutable.{HashMap => Map}
import scala.collection.mutable.Stack
import scala.collection.mutable.Queue
import scala.collection.mutable.ListBuffer

class Congruence {
  val find = new FindTable()
  val sigTable = new SignatureTable()
  val eqTriples = new Map[E,(E,E,App)] //this structure is good for comparing to inequalities
//  val transitivityTripples = new 
  val deduced = new Queue[(E,E)]
  
  var g = new WGraph[E,Set[App]]()
  
  def addEquality(eq: App) = {
    val (l,r) = (eq.function.asInstanceOf[App].argument,eq.argument)
//    println(eq + ", left: " + l + " right: "+ r)
    addNode(l)
    addNode(r)
    merge(l,r,eq)
  }
  
  //find query creates new CCR before subterms are added
   //order matters???
  def addNode(u: E): Unit = {
    if (!find.isDefinedAt(u)) {
      u match {
        case App(v1,v2) => {
          addNode(v1)
          addNode(v2)
        }
        case _ => 
      }
      find.+=(u -> new CCR(u))
      val y = sigTable.query(u, find)
      if (y != u) { //Deduced equality
        union(find.query(u),find.query(y))
//        eqTriples.update(u, (u,y,EmptyEq))
//        eqTriples.update(y, (u,y,EmptyEq))
        deduced.enqueue((u,y))
      }
      else {
        u match {
          case App(v1,v2) => {
            find.query(v1).pred+=(u)
            find.query(v2).pred+=(u)
          }
          case _ => 
        }
      }
    }
  }
  
  def merge(a: E, b: E, eq: App) = {
    val combine = Stack((a,b))
    var stillTransitivity = true
    var e = eq
//    println("merge " + a + " and " + b + " because: " + e)
//    if (stillTransitivity) {
//      g = g.addUndirectedEdge((a,List(e),b), 1)
//    }
    if (!stillTransitivity) {
      deduced.enqueue((a,b))
    }
    while (!combine.isEmpty) {
      val (u,v) = combine.pop
      val findU = find.query(u)
      val findV = find.query(v)
//      println("possibly merge " + (u,v) + " finds: "+ (find(u),find(v)) + " querys: " + (findU,findV))
      if (findU != find(u) || findV != find(v)) {
//        println("merge " + u + " and " + v + " because: " + e)
        deduced.enqueue((u,v))
      }
      if (findU != findV) { 
        combine.pushAll(union(findU,findV))
        eqTriples.update(u, (u,v,e))
        eqTriples.update(v, (u,v,e))
        if (stillTransitivity) { //Transitivity equality
          g = g.addUndirectedEdge((u,Set(e),v), 1)
        }
        else { //Deduced equality
//          println("deduce in merge: " + (u,v))
          deduced.enqueue((u,v))
        }
        stillTransitivity = false
//        e = EmptyEq
      }
    }
  }
  
  def union(a: CCR, b: CCR) = {
    val deduct = ListBuffer[(E,E)]()
    val (x,y) = if (a.term.size > b.term.size) (a,b) else (b,a)
    y.term.foreach(t => {
      find.update(t,x)
    })
    x.term.++=(y.term)
    y.pred.foreach(p => {
      val s = sigTable.query(p,find)
//      if (find.query(p) != find.query(s)) {
//        println("deduct in union: " + (p,s))
        deduced.enqueue((p,s))
        deduct += ((p,s))
//      }
    })
    x.pred.++=(y.pred)
    deduct
  }
  
  def resolveDeduced = {
    val dij = new Dijkstra[E,App]
//    println("deduce: " + deduced)
    while (!deduced.isEmpty) {
      val (u,v) = deduced.dequeue
//      println("resolve " + (u,v))
      u match {
        case App(u1,u2) => {
          v match {
            case App(v1,v2) => {
              val path1 = dij(u1,v1,g)
              
              val labels1 = path1.collectLabels
              val vertices1 = path1.collectVertices
//              val weight1 = vertices1.foldLeft(0)((sum,v) => sum + dij.distances.getOrElse(v, Integer.MAX_VALUE)) //if Integer.Max_Value then should be a bug here
//              val weight1 = dij.distances.getOrElse(v1, Integer.MAX_VALUE)
              
              val path2 = dij(u2,v2,g)
              
              val labels2 = path2.collectLabels
              val vertices2 = path2.collectVertices
//              val weight2 = vertices2.foldLeft(0)((sum,v) => {
//                val d = dij.distances.getOrElse(v, Integer.MAX_VALUE) //if Integer.Max_Value then should be a bug here
//                println("distance of " + v + " to " + u2 + ": " + d)
//                sum + d
//              })
//              val weight2 = dij.distances.getOrElse(v2, Integer.MAX_VALUE)
              val labels = labels1 union labels2
//              val weight = weight1 + weight2
              val weight = labels.size
//              println("w1: " + weight1 + " w2: " + weight2)
//              println("label1: " + labels1 + " label2: " + labels2 + " = " + labels)
              g = g.addUndirectedEdge((u,labels,v), weight)
//              println("deduced :" + u + " ~ " + v + " because: " + labels + " weight: " + weight)
            }
            case _ =>
          }
        }
        case _ =>
      }
    }
  }
  
  def explain(u: E, v: E) = {
    resolveDeduced
    val dij = new Dijkstra[E,App]
    dij(u,v,g)
  }
  
  def isCongruent(u: E, v: E) = {
    if (find.isDefinedAt(u) && find.isDefinedAt(v)) find(u) == find(v)
    else false
  }
  
//  def eqTriplesToGraph:WGraph[E,App] = {
//    val triples = eqTriples.values
//    val (simple,nonSimple) = triples.partition(tr => tr._3 != EmptyEq)
//    simple.foreach(tr => {
//      g = g.addUndirectedEdge((tr._1,tr._3,tr._2), 1)
//    })
//    nonSimple.foreach(tr => {
//      g = resolve(tr._1,tr._2,g)
//    })
//    g
//  }
  
//  def resolve(tr: (E,E,App), g: WGraph[E,App]): WGraph[E,App] = {
//    var g1 = g
//    
//    g1
//  }
}