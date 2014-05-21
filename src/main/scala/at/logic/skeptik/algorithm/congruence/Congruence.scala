package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.algorithm.dijkstra._
//import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet,Queue => MQueue}
import scala.collection.mutable.Stack
import scala.collection.immutable.Queue
import scala.collection.mutable.ListBuffer

/**
 * Class Congruence class is for computing and maintaining the congruence closure of some input equations
 * equations can be entered incrementally and on entering an equation CCRs will be created and/or merged
 * is immutable
 * 
 * @param eqReferences          Map for keeping track of the objects that represent the equalities between tuples of expressions
 * @param find                  Table for relating terms with their CCR
 * @param deduced               List of deduced equalities, for which new explanations can be computed on demand
 * @param g                     Graph representing the congruence closure, with labels of type EqLabel: see at.logic.skeptik.algorithm.dijkstra.package
 */

class Congruence(
    val eqReferences: MMap[(E,E),EqW] = MMap[(E,E),EqW](), 
    val find: FindTable = new FindTable(), 
    val deduced: Queue[(E,E)] = Queue[(E,E)](), 
    val g: WGraph[E,EqLabel] = new WGraph[E,EqLabel]()) {
  
  /**
   * the following methods are create new Congruence objects, when one of their parameters is changed
   */
  def updateFind(newFind: FindTable) = {
    new Congruence(eqReferences, newFind,deduced,g)
  }

  def updateDeduced(newDeduced: Queue[(E,E)]) = {
    new Congruence(eqReferences, find,newDeduced,g)
  }
  def updateGraph(newG: WGraph[E,EqLabel]) = {
    new Congruence(eqReferences, find,deduced,newG)
  }
  

  /**
   * method for adding an equation to the this congruence closure
   * calls addNode for both sides of the equality
   * calls merge with the two sides
   * adds edge labeled with the equality and weight 1 to the graph
   * 
   * see page 188 in Pascal's work
   * 
   * @param eq    equality to be added represented as an EqW object
   * @result      new congruence data structure with eq added
   */
  
  def addEquality(eq: EqW): Congruence = {
    val (l,r) = (eq.l,eq.r)
    val eqRef = eqReferences.update((l,r), eq)
//    val c0 = updateEqReferences(eqRef)
    val c1 = this.addNode(l)
    val c2 = c1.addNode(r)
    val c3 = c2.updateGraph(c2.g.addUndirectedEdge((l,EqLabel(eq,None),r), 1))
    val res = c3.merge(l,r,Some(eq))
    res
  }
  
  /**
   * method addNode adds a term into the congruence closure structure
   * checks the findmap for entry u does nothing when u has an entry
   * adds u and all its subterms to the congruence structure
   * queries for signature equality and deduces new equalities
   * 
   * see page 189 in Pascal's work
   * 
   * @param  u  expression to add to the structure
   * @result new congruence structure with u an its subterms added
   */
  //find query creates new CCR before subterms are added
   //order matters???
  def addNode(u: E): Congruence = {
    val uRepr = find.map.get(u)
    uRepr match {
      case Some(_) => {
        this
      }
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
            val y = c3.find.sigQuery(u)
            y match {
              case Some(v) => {
                val c4 = c3.union(u,v)
                val d = c4.resolveDeduced(u, v)
                d
              }
              case None => {
                val nF = newFind.addPred(v1, u)
                val nF2 = nF.addPred(v2, u)
                val c4 = c3.updateFind(nF2)
                c4
              }
            }
          }
          case _ => c3
        }
      }
    }
  }
  
   /**
   * method for adding lists of equations
   */
  def addAll(eqs: List[EqW]): Congruence = {
    eqs.foldLeft(this)({(A,B) => A.addEquality(B)})
  }
  
  /**
   * merges the CCRs of two by calling union of these terms
   * recursively merges deduced equalities of union
   * 
   * see page 190 in Pascal's work
   * 
   * @param  a,b expression to be merged
   * @param  eq equality as reason for merge
   * @result new congruence structure with CCRs merged

   */
  def merge(a: E, b: E, eq: Option[EqW]): Congruence = {
    val (nF,aF,bF) = find.queryTwo(a, b)
    val c1 = updateFind(nF)
    if (aF != bF) {
      val deduced = MSet[(E,E)]()
      val c2 = c1.union(a,b,deduced)
//      var ded = deduced.p
//      deduced.foldLeft(c2)({(A,B) =>
//              val d = A.resolveDeduced(B._1, B._2)
//        d.merge(B._1, B._2, None) //this line is slowing down the process alot
      var c = c2
      var d = deduced.size
      while (!deduced.isEmpty) {
//        if (d > deduced.size) println("got smaller")
        d = deduced.size
        val (u,v) = deduced.head
        deduced -= ((u,v))
        if (c.find.query(u) != c.find.query(v)) c = c.union(u, v, deduced)
      }
      c
//      var out = c2
//      while (!deduced.isEmpty) {
//        val (l,r) = deduced.pop
//        val (x,newDeduced) = out.union(l,r)
//        val y = x.resolveDeduced(l, r)
//        deduced.pushAll(newDeduced)
//        out = y
//      }
//      out
    }
    else c1
  }
  
  /**
   * union actually performs the merge by altering CCRs and the findMap
   * calls sigQuery to deduce new equalities
   * 
   * see page 191 in Pascal's work 
   * 
   * @param u,v expressions which CRRs should be merged
   * @param deduced mutable map to add deduced equalities to
   * @res new congruence structure with u,v merged and list of deduced equalities
   */
  def union(u: E, v: E, deduced: MSet[(E,E)] = MSet[(E,E)]()): (Congruence) = {
    val (nF,a) = find.query(u)
    val (nF2,b) = nF.query(v)
    
    val (remainCCR,removeCCR,remainTerm,removeTerm) = if (a.term.size > b.term.size) (a,b,u,v) else (b,a,v,u)
    val nF3 = removeCCR.term.foldLeft(nF2)({(A,B) => A.addTerm(remainTerm, B)})
    
    val (nF4,remain) = nF3.query(remainTerm)
    val (nF5,remove) = nF4.query(removeTerm)
    
    val nF6 = remain.term.foldLeft(nF5)({(A,B) => A.update(B, remain)})
    val c1 = updateFind(nF6)
    val c2 = removeCCR.pred.foldLeft(c1)({(A,B) => 
      val s = A.find.sigQuery(B)
      s match {
        case Some(q) => {
//          println("deducing " + (B,q))
//          if (deduced.contains((B,q))) println("adding something, which is already there")
          deduced.+=((B,q))
          A.addDeduced(B, q)
        }
        case None => {
          A
        }
      }
    })
    c2
  }
  
  /**
   * adds one deduced equality to the Queue of deduced equalities
   */
  def addDeduced(u: E, v: E): Congruence = {
    updateDeduced(deduced.enqueue((u,v)))
  }
  
  /**
   * resolves all queued up equalities by finding an explanation for them in the current graph
   */
  def resolveDeducedQueue: Congruence = {
    deduced.foldLeft(this)((A,B) => {
      val c = A.resolveDeduced(B._1,B._2)
      c
    })
  }
  
  /**
   * resolves one given equality by finding an explanation for it in the current graph 
   * and adding an edge labeled with the explanation to the graph
   * the weight of the edge is defined as the size of the explanation
   * 
   * creates a EquationDijkstra object to perform the search
   * 
   * @res congruence structure with updated graph
   */
  def resolveDeduced(u: E, v: E): Congruence = {
    
    u match {
      case App(u1,u2) => {
        v match {
          case App(v1,v2) => {
            val path1 = 
              if (u1 == v1) new EquationPath(u1,None)
              else callDijkstra(u1,v1,g)
            val path2 = 
              if (u2 == v2) new EquationPath(u2,None)
              else callDijkstra(u2,v2,g)
            val eq1 = path1.originalEqs
            val eq2 = path2.originalEqs
            val eqAll = eq1 union eq2
           
            val weight = eqAll.size
            val x = EqW(u,v, eqReferences)
            
            updateGraph(g.addUndirectedEdge((u,EqLabel(x,Some(path1,path2)),v), weight))
          }
          case _ => this
        }
      }
      case _ => this
    }
  }
  
  def callDijkstra(u: E, v: E, g: WGraph[E,EqLabel]) ={
    val dij = new EquationDijkstra(eqReferences)
    dij(u,v,g)
  }
  
  /**
   * queries an EquationDijkstra object for the explanation of the equality of two terms
   * 
   * @res None if there is no explanation (i.e. the terms are not congruent)
   *      Some(eqT) where eqT is an EquationTree representing the explanation
   */
  def explain(u: E, v: E): Option[EquationPath] = {
    val dij = new EquationDijkstra(eqReferences)
    val path = dij(u,v,g)
    if (path.isEmpty) None else Some(path)
  }
  
  /**
   * @res returns true iff u and v are congruent in the current congruence structure
   */
  def isCongruent(u: E, v: E) = {
    find.query(u) == find.query(v)
  }
}