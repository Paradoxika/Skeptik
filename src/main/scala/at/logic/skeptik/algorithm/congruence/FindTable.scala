package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import scala.collection.immutable.{HashMap => Map}
import scala.collection.immutable.{HashMap => IMap}

class FindTable(val map: IMap[E,CCR] = IMap[E,CCR]()) {
  def query(x: E):(FindTable,CCR) = {
    map.get(x) match {
      case Some(ccr) => (this,ccr)
      case None => enter(x).query(x)
    }
  }
  
  def queryTwo(x: E, y: E): (FindTable,CCR,CCR) = {
    val (nF1,xF) = query(x)
    val (nF2,yF) = nF1.query(y)
    (nF2,xF,yF)
  }
  
  def enter(x: E): FindTable = new FindTable(map + (x -> new CCR(x)))
  
  def enter(x: E, c: CCR): FindTable = new FindTable(map + (x -> c))
      
  def delete(x: E): FindTable = new FindTable(map - x)
  
  def update(x: E, c: CCR): FindTable = delete(x).enter(x,c)
  
  def sigQuery(x: E): Option[E] = {
//    println(x + " is queried for sig")
    x match {
      case App(u,v) => {
//        println()
        query(u)._2.pred.find(p => {
          p match {
            case App(_,t) => {
              t != v && query(v)._2 == query(t)._2
            }
            case _ => false
          }
        })
      }
      case _ => None
    }
  }
  
  def addNeighbour(x: E, neighbour: E): FindTable = {
    val (table,ccr) = query(x)
    val newCCR = new CCR(x,ccr.s,ccr.term,ccr.pred,ccr.rightNeighbours + neighbour)
    ccr.term.foldLeft(table)({(A,B) => A.update(B, newCCR)})
  }
  
  def addPred(x: E, pred: E): FindTable = {
    val (table,ccr) = query(x)
//    table.update(x, new CCR(x,ccr.s,ccr.term,ccr.pred + pred))
    val newCCR = new CCR(x,ccr.s,ccr.term,ccr.pred + pred,ccr.rightNeighbours)
    ccr.term.foldLeft(table)({(A,B) => A.update(B, newCCR)})
  }
  
  def addTerm(x: E, term: E): FindTable = {
    val (table,ccr) = query(x)
    val newCCR = new CCR(x,ccr.s,ccr.term + term,ccr.pred ,ccr.rightNeighbours)
    ccr.term.foldLeft(table)({(A,B) => A.update(B, newCCR)})
  }
  
  override def toString = map.mkString(",")
}