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
    val eqReferences: IMap[(E,E),App] = new IMap[(E,E),App], 
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
    new Congruence(newFind, sigTable, eqReferences,deduced,g)
  }
  def updateSigTable(newSigTable: SignatureTable) = {
    new Congruence(find, newSigTable, eqReferences,deduced,g)
  }
  def updateEqReferences(newEqReferences: IMap[(E,E),App]) = {
    new Congruence(find, sigTable, newEqReferences,deduced,g)
  }
  def updateDeduced(newDeduced: Queue[(E,E)]) = {
    new Congruence(find, sigTable, eqReferences,newDeduced,g)
  }
  def updateGraph(newG: WGraph[E,EqLabel]) = {
    new Congruence(find, sigTable, eqReferences,deduced,newG)
  }
  
  def addAll(eqs: List[App]): Congruence = {
    eqs.foldLeft(this)({(A,B) => A.addEquality(B)})
  }
  
  def addEquality(eq: App): Congruence = {
    val (l,r) = (eq.function.asInstanceOf[App].argument,eq.argument)
    val eqRef = eqReferences.updated((l,r), eq)
    val c0 = updateEqReferences(eqRef)
    val c1 = c0.addNode(l)
    val c2 = c1.addNode(r)
    val c3 = c2.updateGraph(c2.g.addUndirectedEdge((l,(eq,None),r), 1))
    val res = c3.merge(l,r,Some(eq))
    res
  }
  
  //find query creates new CCR before subterms are added
   //order matters???
  def addNode(u: E): Congruence = {
    val uRepr = find.map.get(u)
    uRepr match {
      case Some(_) => {
//        println("come here when adding " + u)
        this
      }
      case None => {
//        println("come there when adding " + u)
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
            val y = c3.find.sigQuery(u)
            y match {
              case Some(v) => {
                val c4 = c3.union(u,v)._1
                val d = c4.resolveDeduced(u, v)
                val dd = d.addDeduced(u, v)
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
      deduced.foldLeft(c2)({(A,B) =>
        val d = A.resolveDeduced(B._1, B._2)
//        println("Deducing " + B._1 + " = " + B._2 + " in merge")
        d.merge(B._1, B._2, None)
      })
    }
    else c1
  }
  
  def union(u: E, v: E): (Congruence,ListBuffer[(E,E)]) = {
//    println("union: " + (u,v))
    val (nF,a) = find.query(u)
    val (nF2,b) = nF.query(v)
    
    val deduct = ListBuffer[(E,E)]()
    val (remainCCR,removeCCR,remainTerm,removeTerm) = if (a.term.size > b.term.size) (a,b,u,v) else (b,a,v,u)
    val nF3 = removeCCR.term.foldLeft(nF2)({(A,B) => A.addTerm(remainTerm, B)})
    
    val (nF4,remain) = nF3.query(remainTerm)
    val (nF5,remove) = nF4.query(removeTerm)
    
    val nF6 = remain.term.foldLeft(nF5)({(A,B) => A.update(B, remain)})
    val c1 = updateFind(nF6)
//    println("after union of " + (u,v) + " their finds: " + (c1.find.map(u),c1.find.map(v)))
    val c2 = removeCCR.pred.foldLeft(c1)({(A,B) => 
      val s = A.find.sigQuery(B)
      s match {
        case Some(q) => {
          deduct += ((B,q))
          A.addDeduced(B, q)
        }
        case None => {
          val (finalSig,finalFind) = A.sigTable.enter(B,A.find)
          A.updateFind(finalFind).updateSigTable(finalSig)
        }
      }
    })
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
//            if (u.t != v.t) println("Types are not the same for " + (u,v))
            val x = Eq(u,v)
            if (x.toString == "((f2 c_5 c_2) = c_3)" || x.toString == "(c_3 = (f2 c_5 c_2))") println("creating " + x + " when adding an edge to graph")
            updateGraph(g.addUndirectedEdge((u,(x,Some(path1,path2)),v), weight))
          }
          case _ => this
        }
      }
      case _ => this
    }
  }

  def explain(u: E, v: E): Option[EquationTree] = {
//    resolveDeduced
    val dij = new EquationDijkstra
//    val tmpEq = Eq(u,v)
//    val tmpCon = addEquality(tmpEq)
//    val realG = tmpCon.g.removeUndirectedEdge((u,(tmpEq,None),v))
    val path = dij(u,v,g)
//    if (path.isEmpty) {
//      println("trying to explain " + (u,v) + " but got empty path")
//      (u,v) match {
//        case (App(u1,u2),App(v1,v2)) => {
//          val p1Opt = explain(u1,v1)
//          val p2Opt = explain(u2,v2)
//          println("now trying to explain " + (u1,v1) + " result: " + p1Opt)
//          println("now trying to explain " + (u2,v2) + " result: " + p2Opt)
//          (p1Opt,p2Opt) match {
//            case (Some(p1),Some(p2)) => {
//              if (p1.isEmpty || p2.isEmpty) {
//                None
//              }
//              else {
//                val end = new EquationTree(v,None)
//                val eqTreeEdge = new EqTreeEdgeC(end,(Eq(u,v),Some((p1,p2))))
//                Some(new EquationTree(u,Some(eqTreeEdge)))
//              }
//            }
//            case _ => None
//          }
//        }
//        case _ => None
//      }
//    }
//    else Some(path)
    if (path.isEmpty) None else Some(path)
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