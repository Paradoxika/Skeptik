/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

object Utilities {
  def gcd(a:Int, b:Int) = if (a > b) gcdRec(a,b) else gcdRec(b,a)
  def gcdRec(a:Int, b:Int):Int = if (b==0) a else gcdRec(b, a % b)
  def gcd(list: List[Int]): Int = list match {
    case Nil => 0 // throw new Exception("The list of integers should not be empty.")
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
}
