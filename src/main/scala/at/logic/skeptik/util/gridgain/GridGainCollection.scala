//package at.logic.skeptik.util.gridgain
//
//import org.gridgain.scalar.scalar
//import org.gridgain.scalar.scalar._
//import org.gridgain.grid.GridClosureCallMode._
//
//
//// This collection class provides parallel/distributed methods
//// map and foreach, based on GridGain's mapReduce framework
//class GridGainSeq[+A](val elements: Seq[A]) {
//    
//  def mapReduce[U,V](f: A => U, r: Seq[U] => V): V = {
//    scalar { grid$ @<(SPREAD, for (e <- elements) yield (() => f(e)), r) }
//  } 
//
//  def map[U](f: A => U): Seq[U] = mapReduce(f, (s:Seq[U]) => s)
//  
//  def foreach[U](f: A => U): Unit = map(f)
//}
//object GridGainSeq {
//  def apply[A](elements: A*) = new GridGainSeq(elements)
//}
