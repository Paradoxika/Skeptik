package at.logic.skeptik.congruence

import at.logic.skeptik.expression.formula._
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.congruence.EqW

object EqWTest {
  def main(args: Array[String]):Unit = {
    val t = o
    
    val a = new Var("a",t)
    val b = new Var("b",t)
    val c = new Var("c",t)
    val d = new Var("d",t)
    
    val eq = EqW(a,b,MMap[(E,E),EqW]())
    
    val eq2 = EqW(b,a,MMap[(E,E),EqW]())
    
    val seq = Set(eq)
    println(eq == eq)
    println(seq.contains(eq2))
    println(EqW.isEq(eq.equality))
  }
}