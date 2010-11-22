/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import scala.collection.mutable._

object Utilities {
  def gcd(a:Int, b:Int) = if (a > b) gcdRec(a,b) else gcdRec(b,a)
  def gcdRec(a:Int, b:Int):Int = if (b==0) a else gcdRec(b, a % b)
  def gcd(list: List[Int]): Int = list match {
    case Nil => 0
    case a::Nil => a
    case a::tail => {
      val tailGCD = gcd(tail)
      if (tailGCD == 1) 1 else gcd(a,tailGCD)
    }
  }

  class Counter {private var number = 0;def get:Int={number += 1;return number}}

  def argmin[A](list: List[A], f: Function[A, Int]): (A,Int) = list match {
    case Nil => throw new Exception("List is Empty")
    case head::tail => {
      var currentBestArgument = list.head
      var currentBestValue = f(list.head)
      for (argument <- tail) {
        val value = f(argument)
        if (value < currentBestValue) {
          currentBestValue = value
          currentBestArgument = argument
        }
      }
      return (currentBestArgument,currentBestValue)
    }
  }

  def unite[T](list: List[List[T]]): List[T] = list match {
    case Nil => Nil
    case head::tail => unite(tail) ++ head
  }
  def intersect[T](list: List[List[T]]): List[T] = {
    list match {
      case Nil => Nil
      case head::Nil => head
      case head::tail => head.intersect(intersect(tail))
    }
  }
}
