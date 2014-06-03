package at.logic.skeptik.proof.sequent
package resolution


import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import collection.mutable.Set

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class ContractionSpecification extends SpecificationWithJUnit {

  var usedVars = Set[Var]()
  val x = new Var("X", i)
  val n = new Var("NEW2", i)
  val e = new Var("eq", i -> (i->i))
  val f = new Var("f", i->i)
  val two = new Var("2", i)
  usedVars += x

  
  //First test case
  //(eq (f X) 2), (eq (f NEW2) 2) ⊢
  val f1 = AppRec(e, List(App(f, x), two))
  val f2 = AppRec(e, List(App(f, n), two))
  
//  println("f1: " + f1)
//  println("f2: " + f2)
  
  val seqF2 = Sequent(f2)()
  val seq = f1 +: seqF2
  
//  println(seq)
  
  val premise = new Axiom(seq)

  val con = Contraction(premise)(usedVars)

  
  //Second test case
  //(eq X 2), (eq (f NEW2) 2) ⊢
  val f1B = AppRec(e, List(x, two))
  val f2B = AppRec(e, List(App(f, n), two))
  
  val seqF2B = Sequent(f2B)()
  val seqB = f1B +: seqF2B
  
  val premiseB = new Axiom(seqB)

  val conB = Contraction(premiseB)(usedVars)
  
  "Contraction" should {
    "return the correct resolvent when necessary to make a contract" in {
//           println("ur: " + ur.conclusion)
      Sequent(f2)() must beEqualTo(con.conclusion)
    } 
     "return the correct resolvent when no contraction is possible" in {
//           println("conB: " + ur.conclusion)
      seqB must beEqualTo(conB.conclusion)
    } 
  }
}