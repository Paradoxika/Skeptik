package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.ArrayBuffer

/**
 * abstract class MyPriorityQueue is a priority queue for the Dijkstra algorithm
 * Scala's own priority queues don't support the decreaseKey method, which is crucial for the Dijkstra algorithm
 */

abstract class MyPriorityQueue[T1,T2] {

  def insert(elem: T1, value: T2)
  
  def minimum: Option[T1]
  
  def extractMin: Option[T1]
  
  def decreaseKey(elem: T1, value: T2)
  
  def isEmpty: Boolean
}

/**
 * class ArrayPQ is an array implementation of priority queue
 * using such a priority queue leads to worst case complexity of Disjkstra's algorithm of n^2,
 * whereas a binary min heap can lower the complexity if the graph is sufficiently sparse.
 * A fibonacci heap would decreases the complexity further, but is considered to be impractical.
 * 
 * For details see page 598 of
 * Cormen, T., Leiserson, C., Rivest, R., & Stein, C. (2001). Introduction to algorithms. 
 * Retrieved from http://euler.slu.edu/~goldwasser/courses/loyola/comp363/2003_Spring/handouts/course-info.pdf
 * 
 */
class ArrayPQ[T1,T2 <% Ordered[T2]] extends MyPriorityQueue[T1,T2] {

  val elems = ArrayBuffer[T1]()
  val values = ArrayBuffer[T2]()
  
  def insert(elem: T1, value: T2) = {
    elems.append(elem)
    values.append(value)
  }
  
  def minimum: Option[T1] = {
    if (!elems.isEmpty) {
      val v = elems(values.indexOf(values.min))
      Some(v)
    }
    else None
  }
  
  def extractMin: Option[T1] = {
    if (!elems.isEmpty) {
      val elem = minimum.get
      val n = elems.indexOf(elem)
      values.remove(n)
      elems.remove(n)
      Some(elem)
    }
    else None
  }
  
  def decreaseKey(elem: T1, value: T2) = {
    val n = elems.indexOf(elem)
    values.update(n, value)
  }
  
  def isEmpty: Boolean = elems.isEmpty && values.isEmpty
  
  override def toString = {
    var i = 0
    elems.map(e => {
      val v = values(i)
      i = i + 1
      e + " ~ " + v
    }).mkString(",")
  }
}