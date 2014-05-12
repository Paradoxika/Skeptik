package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import scala.collection.immutable.{HashMap => Map}
import scala.collection.immutable.{HashMap => IMap}

/**
 * immutable class FindTable stores CCRs of expressions (terms)
 * 
 * @param map is the centerpiece of this table, relating expressions to CCRs
 */

class FindTable(val map: IMap[E,CCR] = IMap[E,CCR]()) {
  
  /**
   * query method for the map
   * since the class is immutable, and it insterts newly created CCRs if no mapping exists yet for an expression
   * it has to return a findtable object aswell
   * 
   * Initially I thought this is handy, but now I actually think it is not good to change stuff in a query method
   * also it's actually annoying to have to take into account possible changes everywhere 
   * 
   * @param x expression for which the stored CCR should be returned
   * 
   * @return either the current object and the CCR for x
   *         or a new findTable where x is inserted with default initial values
   */
  def query(x: E):(FindTable,CCR) = {
    map.get(x) match {
      case Some(ccr) => (this,ccr)
      case None => enter(x).query(x)
    }
  }
  
  /**
   * queryTwo performs query for two terms, which is often needed in the code of Congruence
   * when for example two sides of an equation are queried.
   */
  def queryTwo(x: E, y: E): (FindTable,CCR,CCR) = {
    val (nF1,xF) = query(x)
    val (nF2,yF) = nF1.query(y)
    (nF2,xF,yF)
  }
  
  /**
   * enters expression x into the table with a newly created CCR
   */
  def enter(x: E): FindTable = new FindTable(map + (x -> new CCR(x)))
  
  /**
   * enters expression x into the table with a specified CCR
   */
  def enter(x: E, c: CCR): FindTable = new FindTable(map + (x -> c))
  
  /**
   * deletes mapping for expression x
   */
  def delete(x: E): FindTable = new FindTable(map - x)
  
  /**
   * first deletes mapping of x and then adds new mapping with specified CCR
   */
  def update(x: E, c: CCR): FindTable = delete(x).enter(x,c)
  
  /**
   * sigQuery method replaces the signatureTable of Fontaine's algorithm
   * 
   * the signatureTable is problematic when using immutable data structures,
   * because it relies on the fact that some parts of the table (namely CCRs) can change
   * 
   * Since terms in Skeptik are currified (i.e. only one binary function symbol App)
   * the query for an expression in the findMap having the same signature up to congruence classes
   * can be done here comfortably.
   * 
   * two expressions are signature equal iff they are both compound (i.e. of the form App(u,v) and App(s,t))
   * and u is congruent to v and s is congruent to t.
   * 
   * to check for a signature-equal entry in the map, it is first checked if the input is of the form App(u,v)
   * 
   * in case it is, the findMap entry [u] for u is queried.
   * then for all predecessors in [u], it is checked, whether they are of the form App(s,t)
   * and whether [v] == [t], given that either u != s or v != t (i.e. the other expression is not the expression itself).
   * 
   * @param x expression for which the signature should be checked
   * 
   * @res None if no expression in the findTable matches
   */
  def sigQuery(x: E): Option[E] = {
    x match {
      case App(u,v) => {
        query(u)._2.pred.find(p => {
          p match {
            case App(s,t) => {
              (t != v || u != s) && query(v)._2 == query(t)._2
            }
            case _ => false
          }
        })
      }
      case _ => None
    }
  }
  
  /**
   * @param pred predecessor that should be added to the CCR of x
   * @param x expression for which the CCR should be altered
   * 
   * @res new findTable with altered CCR
   */
  
  def addPred(x: E, pred: E): FindTable = {
    val (table,ccr) = query(x)
//    table.update(x, new CCR(x,ccr.s,ccr.term,ccr.pred + pred))
    val newCCR = new CCR(x,ccr.s,ccr.term,ccr.pred + pred,ccr.rightNeighbours)
    ccr.term.foldLeft(table)({(A,B) => A.update(B, newCCR)})
  }
  
    /**
   * @param term that should be added to the CCR of x
   * @param x expression for which the CCR should be altered
   * 
   * @res new findTable with altered CCR
   */
  def addTerm(x: E, term: E): FindTable = {
    val (table,ccr) = query(x)
    val newCCR = new CCR(x,ccr.s,ccr.term + term,ccr.pred ,ccr.rightNeighbours)
    ccr.term.foldLeft(table)({(A,B) => A.update(B, newCCR)})
  }
  
  override def toString = map.mkString(",")
}