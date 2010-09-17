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
}
