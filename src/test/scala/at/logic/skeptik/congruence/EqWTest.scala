package at.logic.skeptik.congruence

import at.logic.skeptik.expression.formula._
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.expression._
import at.logic.skeptik.congruence.structure.EqW

object EqWTest {
  def main(args: Array[String]):Unit = {
    
    implicit val eqReferences = MMap[(E,E),EqW]()
    
    val t = o
    
    val a = new Var("a",t)
    val b = new Var("b",t)
    val c = new Var("c",t)
    val d = new Var("d",t)
    
    val eq = EqW(a,b)
    
    val eq2 = EqW(b,a)
    
    val seq = Set(eq)
    println(eq == eq)
    println(seq.contains(eq2))
    println(EqW.isEq(eq.equality))
  }
}