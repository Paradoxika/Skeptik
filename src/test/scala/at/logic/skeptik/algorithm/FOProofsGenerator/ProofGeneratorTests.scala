package at.logic.skeptik.algorithm.FOProofsGenerator

import at.logic.skeptik.algorithm.compressor.{FOLowerUnits, FORecyclePivots}
import at.logic.skeptik.algorithm.compressor.FOSplit.FOCottonSplit
import at.logic.skeptik.expression.{App, Var, i, o}
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.parser.TPTPParsers.ProofParserCNFTPTP
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution

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
    compressionTests(1000,7)
  }

  def tests(proofN : Int) = {
    val generator = new ProofGenerator(5)
    generator.generateFolder("/home/eze/Escritorio/GeneratedProofs",proofN)
    var rpiN  = 0
    var rpiF  = 0
    var splN  = 0
    var splF  = 0
    var splAv = 0.0
    var rpiAv = 0.0
    var proofAvSize = 0
    for(i <- 1 to proofN) {
      val proof = ProofParserCNFTPTP.read("/home/eze/Escritorio/GeneratedProofs/GeneratedProofs/Proof" + i)
      proofAvSize += countResolutionNodes(proof)

      val vars  = ProofParserCNFTPTP.getVariables
      ProofParserCNFTPTP.reset()
      ProofParserCNFTPTP.resetVariables()
      val cottonSplit = new FOCottonSplit(vars, 1)
      var rpiCompressedProof   : Proof[Node] = null
      var splitCompressedProof : Proof[Node] = null
      try {
        splitCompressedProof = cottonSplit(proof)
      } catch {
        case e : Exception =>
          splF += 1
          splitCompressedProof = proof
      }

      try {
        rpiCompressedProof = FORecyclePivots(proof)
      } catch {
        case e : Exception =>
          rpiF += 1
          rpiCompressedProof = proof
      }

      if (countResolutionNodes(proof) > countResolutionNodes(rpiCompressedProof)) {
        rpiN += 1
        rpiAv += (countResolutionNodes(rpiCompressedProof) * 1.0) / countResolutionNodes(proof)
      }
      if (countResolutionNodes(proof) > countResolutionNodes(splitCompressedProof)) {
        splN += 1
        splAv += (countResolutionNodes(splitCompressedProof) * 1.0) / countResolutionNodes(proof)
        println("FOSplit: " + countResolutionNodes(proof) + " -> " + countResolutionNodes(splitCompressedProof))
      }
    }
    println("Average proof size: " + (proofAvSize * 1.0)/proofN)
    println("FOSplit\nReduced: " + splN + " proof(s)\nFailed in : " + splF + " proof(s)\nThe average compression was to " + splAv/splN)
    println("FORPI\nReduced: " + rpiN + " proof(s)\nFailed in: " + rpiF + " proof(s)\nThe average compression was to " + rpiAv/rpiN)

  }

  def countResolutionNodes(p: Proof[Node]): Int = {
    var count = 0
    for (n <- p.nodes)
      if (n.isInstanceOf[UnifyingResolution])
        count = count + 1
    count
    p.size
  }

  def compressionTests(proofN : Int, height : Int) : Unit = {
    var rpiN  = 0
    var rpiF  = 0
    var splN  = 0
    var splF  = 0
    var splAv = 0.0
    var rpiAv = 0.0
    var proofAvSize = 0

    for(i <- 1 to proofN) {
      val (proof, vars) = proofGenerationTest(height,Sequent()())
      proofAvSize += proof.size

      val cottonSplit = new FOCottonSplit(vars, 1)
      var rpiCompressedProof   : Proof[Node] = null
      var splitCompressedProof : Proof[Node] = null
      try {
        splitCompressedProof = cottonSplit(proof)
      } catch {
        case e : Exception =>
          splF += 1
          splitCompressedProof = proof
      }
      try {
        rpiCompressedProof = FORecyclePivots(proof)
      } catch {
        case e : Exception =>
          rpiF += 1
          rpiCompressedProof = proof
      }

      if (countResolutionNodes(proof) > countResolutionNodes(rpiCompressedProof) && countResolutionNodes(rpiCompressedProof) > countResolutionNodes(proof) / 2) {
        rpiN += 1
        rpiAv += (countResolutionNodes(rpiCompressedProof) * 1.0) / countResolutionNodes(proof)
        println("FORPI: " + countResolutionNodes(proof) + " -> " + countResolutionNodes(rpiCompressedProof))

      }

      if (countResolutionNodes(proof) > countResolutionNodes(splitCompressedProof) && countResolutionNodes(splitCompressedProof) > countResolutionNodes(proof) / 2) {
        splN += 1
        splAv += (countResolutionNodes(splitCompressedProof) * 1.0) / countResolutionNodes(proof)
        println("FOSplit: " + countResolutionNodes(proof) + " -> " + countResolutionNodes(splitCompressedProof))
      }
    }
    println("Average proof size: " + (proofAvSize * 1.0)/proofN)
    println("FOSplit\nReduced: " + splN + " proof(s)\nFailed in : " + splF + " proof(s)\nThe average compression was to " + splAv/splN)
    println("FORPI\nReduced: " + rpiN + " proof(s)\nFailed in: " + rpiF + " proof(s)\nThe average compression was to " + rpiAv/rpiN)
      /*
          val atom = Atom("p",List(Var("V",i),Var("a",i),App(App(Var("f",i->(i->i)),Var("X",i)),Var("b",i))))
          val sequent = Sequent(atom)()
          var com = 0
          try {
            while(n < 100) {
              n += 1
              val (proof, vars) = proofGenerationTest(5,Sequent()())
              println(proof)
              val timeout = 1
              val cottonSplit = new FOCottonSplit(vars, timeout)
              val rpiCompressedProof = FORecyclePivots(proof)
              val splitCompressedProof = cottonSplit(proof)
              if (proof.size > splitCompressedProof.size) {
                println("\n")
                com += 1
                println(compressedProof)
                println((proof.size - compressedProof.size).toString + " node(s) less\nAfter " + n +" proofs\n\n#####################\n")
                return
              } else
                println("NO COMPRESSION\n#####################\n")
            }
            println("Compressed: " + com)
          } catch {
            case e : Exception => main(null)
          }*/
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
        //println("FAIL\n" + e + "\n")
        proofGenerationTest(proofHeight,root)
    }
  }

}
