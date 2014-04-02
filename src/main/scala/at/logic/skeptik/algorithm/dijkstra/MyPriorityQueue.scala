package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.ArrayBuffer

abstract class MyPriorityQueue[T1,T2] {

  def insert(elem: T1, value: T2)
  
  def minimum: T1
  
  def extractMin: T1
  
  def decreaseKey(elem: T1, value: T2)
  
  def isEmpty: Boolean
}

class ArrayPQ[T1,T2 <% Ordered[T2]] extends MyPriorityQueue[T1,T2] {

  val elems = ArrayBuffer[T1]()
  val values = ArrayBuffer[T2]()
  
  def insert(elem: T1, value: T2) = {
    elems.append(elem)
    values.append(value)
  }
  
  def minimum: T1 = {
    val v = elems(values.indexOf(values.min))
//    println("minimum value: " + values.min + " belongs to: " + v)
    v
  }
  
  def extractMin: T1 = {
    val elem = minimum
    val n = elems.indexOf(elem)
    values.remove(n)
    elems.remove(n)
    elem
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