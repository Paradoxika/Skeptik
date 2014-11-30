package at.logic.skeptik.congruence

import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.congruence._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.proof._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue

object CongruenceNewTest {
  
  def main(args: Array[String]) = {
    val testcase = 1
    
    val t = o
    
    val a = new Var("a",t)
    val a1 = new Var("a1",t)
    val a2 = new Var("a2",t)
    val a3 = new Var("a3",t)
    val b = new Var("b",t)
    val b1 = new Var("b1",t)
    val b2 = new Var("b2",t)
    val b3 = new Var("b3",t)
    val c = new Var("c",t)
    val c1 = new Var("c1",t)
    val c2 = new Var("c2",t)
    val c3 = new Var("c3",t)
    
    val d = new Var("d",t)
    val e = new Var("e",t)
    
    val f = new Var("f",Arrow(t,t))
    
    val f1 = new Var("f",Arrow(t,Arrow(t,t)))
    
    val x = new Var("x",Arrow(t,t))
    
    val op = new Var("op",Arrow(t,Arrow(t,t)))
    val e4 = new Var("e4",t)
    val skc1 = new Var("skc1",t)
    val e3 = new Var("e3",t)
    val e1 = new Var("e1",t)
    
    implicit val eqReferences = MMap[(E,E),EqW]()
    
    var con: Congruence = ArrayCon(eqReferences)
    
    
    testcase match {
      case 0 => {
        con = con.addEquality(EqW(a,b)).addEquality(EqW(b,c)).addEquality(c1,c2).addEquality(c2,c3).addEquality(c3,a1)
        println(con.isCongruent(a, c2))
        println(con.rep(a) + " vs " + con.rep(c2))
        con = con.addEquality(c1,a)
        println(con.isCongruent(a, c2))
        println(con.rep(a) + " vs " + con.rep(c2))
      }
      case 1 => {
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,c),d)
        val t3 = App(App(f1,c1),c2)
        con = con.addEquality(a,c).addEquality(b,c).addEquality(c,d).addEquality(c1,c).addEquality(a,c2).addNode(t1).addNode(t2).addNode(t3)
        println(con.isCongruent(t2, t3))
        println(con.lookup.mkString(","))
        println(con.rep.mkString(","))
        println(con.explain(t2, t3))
      }
    }
  }
}