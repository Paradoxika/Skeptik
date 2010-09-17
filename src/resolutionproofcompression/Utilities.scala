/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

object Utilities {
  def gcd(a:Int, b:Int) = if (a > b) gcdRec(a,b) else gcdRec(b,a)
  def gcdRec(a:Int, b:Int):Int = if (b==0) a else gcdRec(b, a % b)
  def gcd(list: List[Int]): Int = list match {
    case a::b::Nil => gcd(a,b)
    case a::b::tail => gcd(gcd(a,b)::tail)
    case _ => throw new Exception("The list of integers should have at least two elements")
  }
}
