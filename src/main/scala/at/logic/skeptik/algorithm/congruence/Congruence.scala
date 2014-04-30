package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.algorithm.dijkstra._
//import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.Stack
import scala.collection.immutable.Queue
import scala.collection.mutable.ListBuffer

//type pT = Option[PathTree[E,Option[PathTree[E]]]]

//trait recType {
//  type X <: PathTree[E,Option[(X,X)]]
//  type Z = String
//}

//bla[PathTree[E,]]

class Congruence(
    val find: FindTable = new FindTable(), 
    val sigTable: SignatureTable = new SignatureTable(), 
    val eqTriples: Map[E,(E,E,App)] = new IMap[E,(E,E,App)], 
    val deduced: Queue[(E,E)] = Queue[(E,E)](), 
    val g: WGraph[E,EqLabel] = new WGraph[E,EqLabel]()) {
  
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
  def updateGraph(newG: WGraph[E,EqLabel]) = {
    new Congruence(find, sigTable, eqTriples,deduced,newG)
  }
  
  def addEquality(eq: App): Congruence = {
    val (l,r) = (eq.function.asInstanceOf[App].argument,eq.argument)
//    println(eq + ", left: " + l + " right: "+ r)
//    println("add equality " + eq + " to this graph: " + g)
    val c1 = addNode(l)
    val c2 = c1.addNode(r)
//    println("after adding the two nodes " + c2.g)
    val c3 = c2.updateGraph(c2.g.addUndirectedEdge((l,(eq,None),r), 1))
    val res = c3.merge(l,r,Some(eq))
//    println("after adding equality " + eq + " graph: " + res.g)
    res
  }
  
  //find query creates new CCR before subterms are added
   //order matters???
  def addNode(u: E): Congruence = {
//    println("add node to this graph: " + g)
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
//                println("deduce in AddNode: " + u + " == " + v)
                val d = c3.resolveDeduced(u, v)
                
                val dd = d.addDeduced(u, v)
//                println("dd g in addNode: " + dd.g)
                dd
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
  
  def merge(a: E, b: E, eq: Option[App]): Congruence = {
    val (nF,aF,bF) = find.queryTwo(a, b)
    val c1 = updateFind(nF)
    if (aF != bF) {
      val (c2, deduced) = c1.union(a,b)
//      val c3 = 
//        if (eq.isDefined) {
//          c2.updateGraph(g.addUndirectedEdge((a,(eq.get,None),b), 1))
//        }
//        else c2
      deduced.foldLeft(c2)({(A,B) =>
        val d = A.resolveDeduced(B._1, B._2)
//        d.addDeduced(B._1, B._2)
//        println("deduce " + B._1 + " ~ " + B._2)
//        println("d <<g>> : " + d.g)
        d.merge(B._1, B._2, None)
      })
    }
    else c1
  }
  
  def merge2(a: E, b: E, eq: App): Congruence = {
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
//            println("add " + (u,v) + " to graph")
//            c2.updateGraph(g.addUndirectedEdge((u,Set(e),v), 1))
            c2
          }
          else { //Deduced equality
//            println("deduce: " + u + " == " + v)
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
//      println("query sigTable for " + B + " result: " + s)
      s match {
        case Some(q) => {
//          println("deduce: " + B + " ==here " + q)
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
//    println("adding " + (u,v))
    updateDeduced(deduced.enqueue((u,v)))
  }
  
  def resolveDeducedQueue: Congruence = {
    deduced.foldLeft(this)((A,B) => {
//      val (pair,newQueue) = A.deduced.dequeue
      val c = A.resolveDeduced(B._1,B._2)
//      c.updateDeduced(newQueue)
//      println("resolving " + B)
      c
    })
  }
  
  def resolveDeduced(u: E, v: E): Congruence = {
    val dij = new EquationDijkstra
//    println("resolve deduced: " + (u,v))
    u match {
      case App(u1,u2) => {
        v match {
          case App(v1,v2) => {
            val path1 = 
              if (u1 == v1) new EquationTree(u1,None)
              else dij(u1,v1,g)
            val path2 = 
              if (u2 == v2) new EquationTree(u2,None)
              else dij(u2,v2,g)
            
//            println("path1: " + path1)
//            println("path2: " + path2)
            val eq1 = path1.allEqs
            val eq2 = path2.allEqs
            val eqAll = eq1 union eq2
           
            val weight = eqAll.size
//            println("resolve deduce: " + (u,v))
//            println("equations: "+ eqAll)
            //if (weight > 0) here?
            val c = updateGraph(g.addUndirectedEdge((u,(Eq(u,v),Some(path1,path2)),v), weight))
//            println(c.g)
            c
          }
          case _ => this
        }
      }
      case _ => this
    }
  }

  def explain(u: E, v: E) = {
//    resolveDeduced
    val dij = new EquationDijkstra
    dij(u,v,g)
  }
  
  def isCongruent(u: E, v: E) = {
    find.query(u) == find.query(v)
  }
  
  
//  def pathTreetoProof(path: EquationTree): Boolean = {
//    path.pred match {
//      case Some((nextPT,label)) => {
//        if (label.size == 1) {
//          val eq = label.last
//          val (u,v) = (path.v,nextPT.v)
//          val (l,r) = (eq.function.asInstanceOf[App].argument,eq.argument)
//          val x = (l==u && r == v)|| (l == v && r == u) && pathTreetoProof(nextPT)
//          if (!x) println(eq + " is not an equality of " + (u,v))
//          else println(eq + " is an equality of " + (u,v))
//          x
//        }
//        else pathTreetoProof(nextPT)
//      }
//      case None => true
//    }
//  }
  
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