package at.logic.skeptik.congruence

import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.algorithm.congruence
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.congruence._
import at.logic.skeptik.algorithm.dijkstra._

object CongruenceDebug {
  def main(args: Array[String]):Unit = {
//    val proof = ProofParserVeriT.read("F:/Proofs/QF_UF/QG-classification/qg6/iso_icl_sk004.smt2")
//    CongruenceTest(proof)
    val testcase = 0
    
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
    
    var con = new Congruence
    
    val dij = new EquationDijkstra
    
    testcase match {
      case 0 => {
        //a = b; b = c; f(a) = d; f(c) = e; 
        
        val t1 = new App(f,a)
        val t2 = new App(f,c)
        
        val eq1 = Eq(a,b)
        val eq2 = Eq(b,c)
        
        val eq3 = Eq(t1,d)
        val eq4 = Eq(t2,e)
        
        
        
        con = con.addEquality(eq1)
        con = con.addEquality(eq2)
        con = con.addEquality(eq3)
        con = con.addEquality(eq4)
        
        con = con.resolveDeducedQueue
        
        println(con.find)
        println(con.g)
        val path = dij(e,d,con.g)
    //    println(t1 + " = " + t2 + " because: " + con.explain(t1, t2).collectLabels)
        println(e + " = " + d + " because: " + path.allEqs)
        
//        println("trans chain?: " + con.pathTreetoProof(path))
      }
      case 1 => {
        
        //a = b1, b1 = b2, b2 = b3, b3 = c, f(a1)=a, f(c1) = c, a1 = c1
//        val t1 = App(App(f,a1),a1)
//        val t2 = App(App(f,c1),c1)
        
        val t1 = App(f,a1)
        val t2 = App(f,c1)
        
        con = con.addEquality(Eq(a,b1))
        con = con.addEquality(Eq(b1,b2))
        con = con.addEquality(Eq(b2,b3))
        con = con.addEquality(Eq(b3,c))
        con = con.addEquality(Eq(t1,a))
        con = con.addEquality(Eq(t2,c))
        con = con.addEquality(Eq(a1,c1))
        
//        con.resolveDeduced
        
        println(con.find)
        println(con.g)
        
        val path = dij(a,c,con.g)
        println("distance of " + c + " to " + a + ": " + dij.distances.getOrElse(c,Integer.MAX_VALUE))
        println(a + " = " + c + " because: " + path.collectLabels)
        
        con = con.resolveDeducedQueue
//        con = con.resolveDeduced(t1, t2)
        val path2 = dij(a,c,con.g)
        println("distance after " + c + " to " + a + ": " + dij.distances.getOrElse(c,Integer.MAX_VALUE))
        println(a + " = " + c + " because: " + path2.collectLabels)
      }
      case 2 => {
        //a1 = b1, a1 = c1, f(a1) = a, f(b1) = b, f(c1) = c
        val t1 = App(f,a1)
        val t2 = App(f,b1)
        val t3 = App(f,c1)
        
        con = con.addEquality(Eq(a1,b1))
        con = con.addEquality(Eq(a1,c1))
        con = con.addEquality(Eq(t1,a))
        con = con.addEquality(Eq(t2,b))
        con = con.addEquality(Eq(t3,c))
        
//        con.resolveDeduced
        
        val path = dij(a,c,con.g)
        println(con.g)
        println(con.sigTable)
        println("distance of " + c + " to " + a + ": " + dij.distances.getOrElse(c,Integer.MAX_VALUE))
        println(a + " = " + c + " because: " + path.collectLabels)
      }
      
      case _ => {
        //g(l,h) = d, c = d, g(l,d) = a, e = c, e = b, b = h
        
        val g = new Var("g",Arrow(t,Arrow(t,t)))
        val l = new Var("l",t)
//        val i = new Var("i",Arrow(i,i))
        val h = new Var("h",t)
        
        val t1 = App(App(g,l),h)
        val t2 = App(App(g,l),d)
        
        con = con.addEquality(Eq(t1,d))
        con = con.addEquality(Eq(c,d))
        con = con.addEquality(Eq(t2,a))
        con = con.addEquality(Eq(e,c))
        con = con.addEquality(Eq(e,b))
        con = con.addEquality(Eq(b1,b))
        con = con.addEquality(Eq(b1,h))
        
//        con = con.resolveDeducedQueue
        
        val path = dij(a,b,con.g)
        println(con.g)
        println("distance of " + a + " to " + b + ": " + dij.distances.getOrElse(b,Integer.MAX_VALUE))
        println(a + " = " + b + " because: " + path.collectLabels)
        
        con = con.addEquality(Eq(d,c1))
//        con = con.addEquality(Eq(c1,c2))
        con = con.addEquality(Eq(c1,c2))
        con = con.addEquality(Eq(c2,c3))
        con = con.addEquality(Eq(c3,h))
        
        con = con.resolveDeducedQueue
        
        val dij2 = new EquationDijkstra
        
        val path2 = dij2(a,b,con.g)
        println(con.g)
        println("distance of " + a + " to " + b + ": " + dij2.distances.getOrElse(b,Integer.MAX_VALUE))
        println(a + " = " + b + " because: " + path2.collectLabels)
        
//        println("trans chain?: " + path2.toProof)
      }
    }
    
  }
}