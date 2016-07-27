package at.logic.skeptik.algorithm.FOProofsGenerator

import at.logic.skeptik.expression.{App, Var, i, o}
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}


/**
  * Created by eze on 2016.07.25..
  */
object ProofGeneratorTests {
  def main(arfs : Array[String]) = {
    //safeSymbolsTest()
    //testContraction()
    randomLiteralTest()
  }

  def testContraction() = {
    val generator = new ProofGenerator(10)
    val atom = Atom("p",List(Var("V",i),Var("a",i),App(App(Var("f",i->(i->i)),Var("X",i)),Var("b",i))))
    println(generator.generateContraction(Sequent(atom)()))
  }


  def safeSymbolsTest() = {
    val generator = new ProofGenerator(10)
    // Here atom represents: p(V,a,f(X,b))
    val atom = Atom("p",List(Var("V",i),Var("a",i),App(App(Var("f",i->(i->i)),Var("X",i)),Var("b",i))))
    generator.saveSymbols(atom)
    generator.printState
  }

  def randomLiteralTest() = {
    val generator = new ProofGenerator(10)
    println(generator.generateRandomLiteral())
  }

}
