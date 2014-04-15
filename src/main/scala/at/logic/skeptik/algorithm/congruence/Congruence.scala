package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.algorithm.dijkstra._
//import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.immutable.Stack
import scala.collection.immutable.Queue
import scala.collection.mutable.ListBuffer

class Congruence(val find: FindTable = new FindTable(), val sigTable: SignatureTable = new SignatureTable(), val eqTriples: Map[E,(E,E,App)] = new IMap[E,(E,E,App)], val deduced: Queue[(E,E)] = Queue[(E,E)](), val g: WGraph[E,Set[App]] = new WGraph[E,Set[App]]()) {
//  val find = new FindTable()
//  val sigTable = new SignatureTable()
//  val eqTriples = new Map[E,(E,E,App)] //this structure is good for comparing to inequalities
////  val transitivityTripples = new 
//  val deduce1d = Queue[(E,E)]()
//  
//  var g = new WGraph[E,Set[App]]()
  
//  def copy = 
  
  def updateFind(newFind: FindTable) = {
    new Congruence(newFind, sigTable, eqTriples,deduced,g)
  }
  def updateSigTable(newSigTable: SignatureTable) = {
    new Congruence(find, newSigTable, eqTriples,deduced,g)
  }
  def updateEqTriples(newEqTriples: Map[E,(E,E,App)]) = {
    new Congruence(find, sigTable, newEqTriples,deduced,g)
  }
  def updateDeduced(newDeduced: Queue[(E,E)]) = {
    new Congruence(find, sigTable, eqTriples,newDeduced,g)
  }
  def updateGraph(newG: WGraph[E,Set[App]]) = {
    new Congruence(find, sigTable, eqTriples,deduced,newG)
  }
  
  def addEquality(eq: App): Congruence = {
    val (l,r) = (eq.function.asInstanceOf[App].argument,eq.argument)
//    println(eq + ", left: " + l + " right: "+ r)
    val c1 = addNode(l)
    val c2 = c1.addNode(r)
    c2.merge(l,r,eq)
  }
  
  //find query creates new CCR before subterms are added
   //order matters???
  def addNode(u: E): Congruence = {
    val uRepr = find.map.get(u)
    uRepr match {
      case Some(_) => this
      case None => {
        val c2 = 
          u match {
            case App(v1,v2) => {
              val c1 = addNode(v1)
              c1.addNode(v2)
            }
            case _ => this
          }
        val newFind = c2.find.enter(u)
        val c3 = c2.updateFind(newFind)
        u match {
          case App(v1,v2) => {
//            val y = c3.sigTable.query(u, c3.find)
            val y = c3.find.sigQuery(u)
//            println("query sigTable for: " + u + " result: " + y)
//            println("sigT: " + c3.sigTable)
//            println("find: " + c3.find)
            y match {
              case Some(v) => {
//                val newURepr = newFind.query(u).get //has to be there, because it was just added
//    //            val newVRepr = newFind.query(v)
//                val evenNewerFind = newFind.query(v) match {
//                  case Some(u) => newFind
//                  case None => newFind.enter(v)
//                }
//                val newVRepr = evenNewerFind.query(v).get
//                val c5 = c3.updateFind(evenNewerFind)
////                  val c5 = new Congruence(evenNewerFind, sigTable, eqTriples, deduced, g)
                val c4 = c3.union(u,v)._1
                println("deduce: " + u + " == " + v)
                val d = c3.resolveDeduced(u, v)
                d.addDeduced(u, v)
              }
              case None => {
                val nF = newFind.addPred(v1, u)
                val nF2 = nF.addPred(v2, u)
                val c4 = c3.updateFind(nF2)
                val (finalSig,finalFind) = c4.sigTable.enter(u,c4.find)
                c4.updateFind(finalFind).updateSigTable(finalSig)
              }
            }
          }
          case _ => c3
        }
      }
    }
  }
  
  def merge(a: E, b: E, eq: App): Congruence = {
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
    val x = combine.foldLeft(this)({(A,B) => 
      val (u,v) = B
      val (nF,findU) = A.find.query(u)
      val (nF2,findV) = nF.query(v)
      val c1 = A.updateFind(nF2)
//      println("possibly merge " + (u,v) + " finds: "+ (find(u),find(v)) + " querys: " + (findU,findV))
//      if (findU != find(u) || findV != find(v)) {
////        println("merge " + u + " and " + v + " because: " + e)
//        deduced.enqueue((u,v))
//      }
      if (findU != findV) {
//        println("find before union " +A.find)
        val (c2, deduced) = A.union(u,v)
//        println("find after union " +c2.find)
        combine.pushAll(deduced)
//        eqTriples.update(u, (u,v,e))
//        eqTriples.update(v, (u,v,e))
        val c3 = 
          if (stillTransitivity) { //Transitivity equality
            println("add " + (u,v) + " to graph")
            c2.updateGraph(g.addUndirectedEdge((u,Set(e),v), 1))
          }
          else { //Deduced equality
            println("deduce: " + u + " == " + v)
            val d = c2.resolveDeduced(u, v)
            d.addDeduced(u, v)
          }
        stillTransitivity = false
//        e = EmptyEq
        c3
      }
      else c1
    })
//    println("find afterwards: " + x.find)
    x
  }
  
  def union(u: E, v: E): (Congruence,ListBuffer[(E,E)]) = {
//    println("find before : " + find)
    val (nF,a) = find.query(u)
    val (nF2,b) = nF.query(v)
    
    val deduct = ListBuffer[(E,E)]()
    val (remainCCR,removeCCR,remainTerm,removeTerm) = if (a.term.size > b.term.size) (a,b,u,v) else (b,a,v,u)
    val nF3 = removeCCR.term.foldLeft(nF2)({(A,B) => A.addTerm(remainTerm, B)})
    
    val (nF4,remain) = nF3.query(remainTerm)
    val (nF5,remove) = nF4.query(removeTerm)
    
    val nF6 = remain.term.foldLeft(nF5)({(A,B) => A.update(B, remain)})
//    println("find after : " + nF6)
    val c1 = updateFind(nF6)
//    println("removeCCR: " + removeCCR + " its preds: " + removeCCR.pred)
    val c2 = removeCCR.pred.foldLeft(c1)({(A,B) => 
//      val s = A.sigTable.query(B,A.find)
      val s = A.find.sigQuery(B)
      println("query sigTable for " + B + " result: " + s)
      s match {
        case Some(q) => {
          println("deduce: " + B + " ==here " + q)
          deduct += ((B,q))
          A.addDeduced(B, q)
//          A
        }
        case None => {
//          println("sigTable before: " + A.sigTable)
//          val c = A.updateSigTable(A.sigTable.enter(B))
          val (finalSig,finalFind) = A.sigTable.enter(B,A.find)
          A.updateFind(finalFind).updateSigTable(finalSig)
//          println("sigTable after: " + c)
//          c
        }
      }
        
//      }
    })
//    x.pred.++=(y.pred)
    (c2,deduct)
  }
  
  def addDeduced(u: E, v: E): Congruence = {
    println("adding " + (u,v))
    updateDeduced(deduced.enqueue((u,v)))
  }
  
  def resolveDeducedQueue: Congruence = {
    deduced.foldLeft(this)((A,B) => {
//      val (pair,newQueue) = A.deduced.dequeue
      val c = A.resolveDeduced(B._1,B._2)
//      c.updateDeduced(newQueue)
      println("resolving " + B)
      c
    })
  }
  
  def resolveDeduced(u: E, v: E): Congruence = {
    val dij = new Dijkstra[E,App]
    u match {
      case App(u1,u2) => {
        v match {
          case App(v1,v2) => {
            val path1 = dij(u1,v1,g)
            val labels1 = path1.collectLabels
            val path2 = dij(u2,v2,g)
            val labels2 = path2.collectLabels
            val labels = labels1 union labels2
            val weight = labels.size
            new Congruence(find, sigTable, eqTriples, deduced, g.addUndirectedEdge((u,labels,v), weight))
          }
          case _ => this
        }
      }
      case _ => this
    }
  }
  
//  def resolveDeduced: Congruence = {
//    val dij = new Dijkstra[E,App]
////    println("deduce: " + deduced)
//    while (!deduced.isEmpty) {
//      val (u,v) = deduced.dequeue
////      println("resolve " + (u,v))
//      u match {
//        case App(u1,u2) => {
//          v match {
//            case App(v1,v2) => {
//              val path1 = dij(u1,v1,g)
//              
//              val labels1 = path1.collectLabels
//              val vertices1 = path1.collectVertices
////              val weight1 = vertices1.foldLeft(0)((sum,v) => sum + dij.distances.getOrElse(v, Integer.MAX_VALUE)) //if Integer.Max_Value then should be a bug here
////              val weight1 = dij.distances.getOrElse(v1, Integer.MAX_VALUE)
//              
//              val path2 = dij(u2,v2,g)
//              
//              val labels2 = path2.collectLabels
//              val vertices2 = path2.collectVertices
////              val weight2 = vertices2.foldLeft(0)((sum,v) => {
////                val d = dij.distances.getOrElse(v, Integer.MAX_VALUE) //if Integer.Max_Value then should be a bug here
////                println("distance of " + v + " to " + u2 + ": " + d)
////                sum + d
////              })
////              val weight2 = dij.distances.getOrElse(v2, Integer.MAX_VALUE)
//              val labels = labels1 union labels2
////              val weight = weight1 + weight2
//              val weight = labels.size
////              println("w1: " + weight1 + " w2: " + weight2)
////              println("label1: " + labels1 + " label2: " + labels2 + " = " + labels)
//              g = g.addUndirectedEdge((u,labels,v), weight)
////              println("deduced :" + u + " ~ " + v + " because: " + labels + " weight: " + weight)
//            }
//            case _ =>
//          }
//        }
//        case _ =>
//      }
//    }
//  }
  
  def explain(u: E, v: E) = {
//    resolveDeduced
    val dij = new Dijkstra[E,App]
    dij(u,v,g)
  }
  
  def isCongruent(u: E, v: E) = {
    find.query(u) == find.query(v)
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