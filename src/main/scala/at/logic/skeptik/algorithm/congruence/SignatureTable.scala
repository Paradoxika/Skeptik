package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashMap => Map} // possibly try to avoid use of mutable hashmap

class SignatureTable {
  
  val signatures = Map[(E,E),E]()
  
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
  def query(x:E, find: FindTable):E = {
    x match {
      case App(t1,t2) => {
        val s1 = find.query(t1).s
        val s2 = find.query(t2).s
        signatures.getOrElseUpdate((s1,s2), x)
      }
      case _ => x
    }
  }
}