package at.logic.skeptik.algorithm.FOProofsGenerator

import at.logic.skeptik.algorithm.compressor.{FOLowerUnits, FORecyclePivotsWithIntersection}
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
    //testContraction()
    //randomLiteralTest()
    compressionTests(1000,7,1000)
    //tests(1000,7,1)
    //f()
  }

  def f() : Unit = {
    var proof : Proof[Node] = null
    try {
      while (true) {
        proof = proofGenerationTest(2, Sequent()())._1
        FORecyclePivotsWithIntersection(proof)
      }
    } catch {
      case e : Exception =>
        println("\n" + proof)
        println("\n" + e)
    }
  }

  def tests(proofN : Int, height : Int, timeout : Int) = {
    val generator = new ProofGenerator(height)
    generator.generateFolder("/home/eze/Escritorio/GeneratedProofs", proofN, Sequent()())
    var proofsLenghtsSum      = 0
    var rpiProofsLenghtsSum   = 0
    var splitProofsLenghtsSum = 0
    var rpiN      = 0
    var rpiF      = 0
    var splN      = 0
    var splF      = 0
    var splAv     = 0.0
    var rpiAv     = 0.0
    //var splitFail = 0

    for(i <- 1 to proofN) {
      val proof = ProofParserCNFTPTP.read("/home/eze/Escritorio/GeneratedProofs/GeneratedProofs/Proof" + i)
      proofsLenghtsSum += proof.size

      val vars  = ProofParserCNFTPTP.getVariables
      ProofParserCNFTPTP.reset()
      ProofParserCNFTPTP.resetVariables()
      val cottonSplit = new FOCottonSplit(vars, timeout)
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
        rpiCompressedProof = FORecyclePivotsWithIntersection(proof)
      } catch {
        case e : Exception =>
          rpiF += 1
          rpiCompressedProof = proof
      }

      if (countResolutionNodes(proof) > countResolutionNodes(rpiCompressedProof)
        && countResolutionNodes(rpiCompressedProof) > countResolutionNodes(proof) / 2) {
        rpiN += 1
        rpiProofsLenghtsSum += rpiCompressedProof.size
        rpiAv += (countResolutionNodes(rpiCompressedProof) * 1.0) / countResolutionNodes(proof)
        println("FORPI: " + countResolutionNodes(proof) + " -> " + countResolutionNodes(rpiCompressedProof))
      } else
        rpiProofsLenghtsSum += proof.size

      if (countResolutionNodes(proof) > countResolutionNodes(splitCompressedProof)
        && splitCompressedProof.root.conclusion.ant.isEmpty
        && splitCompressedProof.root.conclusion.suc.isEmpty
        && countResolutionNodes(splitCompressedProof) > countResolutionNodes(proof) / 2) {
        splN += 1
        splitProofsLenghtsSum += splitCompressedProof.size
        splAv += (countResolutionNodes(splitCompressedProof) * 1.0) / countResolutionNodes(proof)
        println("FOSplit: " + countResolutionNodes(proof) + " -> " + countResolutionNodes(splitCompressedProof))
      } else if(splitCompressedProof.root.conclusion.ant.nonEmpty || splitCompressedProof.root.conclusion.suc.nonEmpty) {
        //splitFail += 1
        splitProofsLenghtsSum += proof.size
      } else
        splitProofsLenghtsSum += proof.size
    }
    println("Average proof size: " + (proofsLenghtsSum * 1.0)/proofN)
    println("FOSplit\nReduced: " + splN + " proof(s)\nFailed in : " + splF + " proof(s)\nThe average compression was to " + splAv/splN)
    println("Total compression ratio: " + ((proofsLenghtsSum - splitProofsLenghtsSum)*1.0)/proofsLenghtsSum)
    println("FORPI\nReduced: " + rpiN + " proof(s)\nFailed in: " + rpiF + " proof(s)\nThe average compression was to " + rpiAv/rpiN)
    println("Total compression ratio: " + ((proofsLenghtsSum - rpiProofsLenghtsSum)*1.0)/proofsLenghtsSum)
  }

  def countResolutionNodes(p: Proof[Node]): Int = p.size

  def compressionTests(proofN : Int, height : Int, timeout : Int) : Unit = {
    var proofsLenghtsSum = 0
    var rpiProofsLenghtsSum = 0
    var splitProofsLenghtsSum = 0
    var rpiN      = 0
    var rpiF      = 0
    var splN      = 0
    var splF      = 0
    var splAv     = 0.0
    var rpiAv     = 0.0
    var splitFail = 0
    for(i <- 1 to proofN) {
      val (proof, vars) = proofGenerationTest(height,Sequent()())
      proofsLenghtsSum += proof.size

      val cottonSplit = new FOCottonSplit(vars, timeout)
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
        rpiCompressedProof = FORecyclePivotsWithIntersection(proof)
      } catch {
        case e : Exception =>
          rpiF += 1
          rpiCompressedProof = proof
      }

      if (countResolutionNodes(proof) > countResolutionNodes(rpiCompressedProof)
        && countResolutionNodes(rpiCompressedProof) > countResolutionNodes(proof) / 2) {
        rpiN += 1
        rpiProofsLenghtsSum += rpiCompressedProof.size
        rpiAv += (countResolutionNodes(rpiCompressedProof) * 1.0) / countResolutionNodes(proof)
        println("FORPI: " + countResolutionNodes(proof) + " -> " + countResolutionNodes(rpiCompressedProof))
      } else
        rpiProofsLenghtsSum += proof.size

      if (countResolutionNodes(proof) > countResolutionNodes(splitCompressedProof)
        && splitCompressedProof.root.conclusion.ant.isEmpty
        && splitCompressedProof.root.conclusion.suc.isEmpty
        && countResolutionNodes(splitCompressedProof) > countResolutionNodes(proof) / 2) {
        splN += 1
        splitProofsLenghtsSum += splitCompressedProof.size
        splAv += (countResolutionNodes(splitCompressedProof) * 1.0) / countResolutionNodes(proof)
        println("FOSplit: " + countResolutionNodes(proof) + " -> " + countResolutionNodes(splitCompressedProof))
      } else if(splitCompressedProof.root.conclusion.ant.nonEmpty || splitCompressedProof.root.conclusion.suc.nonEmpty) {
        splitFail += 1
        splitProofsLenghtsSum += proof.size
      } else
        splitProofsLenghtsSum += proof.size
    }

    println("Average proof size: " + (proofsLenghtsSum * 1.0)/proofN)
    println("FOSplit\nReduced: " + splN + " proof(s)\nFailed in : " + splF + " proof(s)\nThe average compression was to " + splAv/splN)
    println("Total compression ratio: " + ((proofsLenghtsSum - splitProofsLenghtsSum)*1.0)/proofsLenghtsSum)
    println("Number of fails: " + splitFail)
    println("FORPI\nReduced: " + rpiN + " proof(s)\nFailed in: " + rpiF + " proof(s)\nThe average compression was to " + rpiAv/rpiN)
    println("Total compression ratio: " + ((proofsLenghtsSum - rpiProofsLenghtsSum)*1.0)/proofsLenghtsSum)
  }

  def testContraction() = {
    val generator = new ProofGenerator(10)
    val atom = Atom("p",List(Var("V",i),Var("a",i),App(App(Var("f",i->(i->i)),Var("X",i)),Var("b",i))))
    println(generator.generateContraction(Sequent(atom)()))
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
