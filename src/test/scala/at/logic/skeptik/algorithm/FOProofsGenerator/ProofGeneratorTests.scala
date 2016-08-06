package at.logic.skeptik.algorithm.FOProofsGenerator

import at.logic.skeptik.algorithm.compressor.{FOLowerUnits, FORecyclePivots}
import at.logic.skeptik.algorithm.compressor.FOSplit.FOCottonSplit
import at.logic.skeptik.expression.{App, Var, i, o}
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.parser.TPTPParsers.ProofParserCNFTPTP
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import collection.mutable.{Set => MSet}
import at.logic.skeptik.proof.Proof

/**
  * Created by eze on 2016.07.25..
  */
object ProofGeneratorTests {
  var n = 0

  def main(arfs : Array[String]) : Unit = {
    //safeSymbolsTest()
    //testContraction()
    //randomLiteralTest()

    val generator = new ProofGenerator(3)
    generator.generateFolder("/home/eze/Escritorio",4)
    for(i <- 1 to 4) {
      val p = ProofParserCNFTPTP.read("/home/eze/Escritorio/GeneratedProofs/Proof" + i)
      println(p)
    }
  }

  def compressionTests() = {
    val atom = Atom("p",List(Var("V",i),Var("a",i),App(App(Var("f",i->(i->i)),Var("X",i)),Var("b",i))))
    val sequent = Sequent(atom)()
    var com = 0
    try {
      while(n < 100) {
        n += 1
        val (proof, vars) = proofGenerationTest(7,Sequent()())
        println(proof)
        val timeout = 1
        val cottonSplit = new FOCottonSplit(vars, timeout)
        val compressedProof =
        //FORecyclePivots(proof)
          cottonSplit(proof)
        if (proof.size > compressedProof.size) {
          println("\n")
          com += 1
          println(compressedProof)
          println((proof.size - compressedProof.size).toString + " node(s) less\nAfter " + n +" proofs\n\n#####################\n")
        } else
          println("NO COMPRESSION\n#####################\n")
      }
      println("Compressed: " + com)
    } catch {
      case e : Exception => main(null)
    }
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

  def generateResolutionTest() = {
    val generator = new ProofGenerator(10)
    println(generator.generateResolution(Sequent()()))
    println("")
  }

  def proofGenerationTest(proofHeight : Int, root : Sequent) : (Proof[Node],MSet[Var]) = {
    val generator = new ProofGenerator(proofHeight)
    try {
      (generator.generateProof(root),generator.getVariables())
    } catch {
      case e : Exception =>
        println("FAIL\n" + e + "\n")
        proofGenerationTest(proofHeight,root)
    }
  }

}
