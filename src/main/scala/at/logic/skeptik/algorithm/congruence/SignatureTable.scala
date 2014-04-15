package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashMap => Map} // possibly try to avoid use of mutable hashmap

class SignatureTable(map: IMap[(CCR,CCR),E] = IMap[(CCR,CCR),E]()) {
  
//  val signatures = Map[(E,E),E]()
  
//  def enter(x: E, find: FindTable) = {
//    x match {
//      case App(t1,t2) => {
//        val s1 = find.query(t1).s
//        val s2 = find.query(t2).s
//        new SignatureTable(signatures+((s1,s2) -> x))
//      }
//      case _ => this
//    }
//  }

  // Possibly enter and query can be merged
  // query(x) returns x instead of \emptyset
  
  override def toString = {
    map.mkString(", ")
  }
  
  def query(x:E, find: FindTable): Option[E] = {
    x match {
      case App(t1,t2) => {
//        println("find entering query " + x + " " + find)
        val (nF,u1) = find.query(t1)
        val (nF2,u2) = nF.query(t2)
//        println("find of u2: " + u2 + " in " + nF2)
//        println("find leaving query: " + nF2)
//        println("query : " + (u1,u2) + " in: " + this + " result: " + map.get(u1,u2))
        map.get(u1,u2)
      }
      case _ => None
    }
  }
  
  def enter(x: E, find: FindTable): (SignatureTable,FindTable) = {
    x match {
      case App(t1,t2) => {
        val (nF,findT1) = find.query(t1)
        val (nF2,findT2) = nF.query(t2)
        (new SignatureTable(map + ((findT1,findT2) -> x)),nF2)
      }
      case _ => (this,find)
    }
  }
  
  def delete(x: E, find: FindTable): SignatureTable = {
    x match {
      case App(t1,t2) => {
        val (nF,findT1) = find.query(t1)
        val (_,findT2) = nF.query(t2)
        new SignatureTable(map - ((findT1,findT2)))
      }
      case _ => this
    }
  }
}