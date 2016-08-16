package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.resolution.{FOSubstitution, Contraction, UnifyingResolution}
import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.parser.TPTPParsers.ProofParserCNFTPTP

import collection.mutable.{HashSet => MSet}
import java.io.PrintWriter

import at.logic.skeptik.algorithm.compressor.FOSplit.FOCottonSplit
import at.logic.skeptik.algorithm.FOProofsGenerator.{ProofGenerator,ProofToTPTPFile}
import at.logic.skeptik.expression.{Var, i}
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.sequent.lk.Axiom

import scala.io.Source


object SmallTest {
  def main(args : Array[String]) : Unit = {
    val vars = MSet[Var](Var("V0", i), Var("V1", i), Var("V2", i), Var("V3", i), Var("V4", i), Var("V5", i), Var("V6", i))
    val a1 = Atom("p", List(Var("V1", i)))
    val a2 = Atom("q", List(Var("V2", i), Var("V3", i)))
    val seq1 = Sequent(a1, a2)()
    val a3 = Atom("q", List(Var("V4", i), Var("V5", i)))
    val seq2 = Sequent()(a3)
    val a4 = Atom("p", List(Var("V6", i)))
    val seq3 = Sequent(a4)()
    val a5 = Atom("p", List(Var("V0", i)))
    val a6 = Atom("p", List(Var("c0", i)))
    val seq4 = Sequent()(a5, a6)

    val res1 = UnifyingResolution.resolve(Axiom(seq1), Axiom(seq2), Sequent(a1)(), vars)
    val res2 = UnifyingResolution.resolve(Axiom(seq3), Axiom(seq4), Sequent()(a5), vars)
    val root = UnifyingResolution.resolve(res1, res2, Sequent()(), vars)
    val proof = Proof(root)
    println(proof)


    println((new FOCottonSplit(vars,1))(proof))
  }
}
/**
  * This object is created to run experiments with the FOSpliting Algorithm
  */
object FOSplittingExperiment {

  def countNonResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes)
      if (!n.isInstanceOf[UnifyingResolution])
        count = count + 1
    count
  }

  def countFOSub(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes)
      if (n.isInstanceOf[FOSubstitution])
        count = count + 1
    count
  }

  def countResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes)
      if (n.isInstanceOf[UnifyingResolution])
        count = count + 1
    count
  }

  def getProblems(file: String, path: String): MSet[String] = {
    val outTj = MSet[String]()

    for (line <- Source.fromFile(file).getLines()) {
      val newProblemN = path + line
      println(newProblemN)
      outTj.add(newProblemN)
    }
    outTj
  }

  def main(args: Array[String]): Unit = {

    val path = "/home/eze/Escritorio/Skeptik/GoodProofs/ALL/"
    val proofList = "/home/eze/Escritorio/Skeptik/GoodProofs/ALL/list.txt"

    val problemSetS = getProblems(proofList, path)
    var totalCountT = 0

    //val etempT = new PrintWriter("results-FOSplitting.log")
    val report = new PrintWriter("report-FOSplitting-10.log")
    //val header = "proof,compressed?,length,resOnlyLength,compressedLengthAll,compressedLengthResOnly,compressTime,compressRatio,compressSpeed,compressRatioRes,compressSpeedRes,numFOSub,totalTime"
    //etempT.println(header)
    //etempT.flush()
    val noDataString = ",-1,-1,-1,-1,-1,-1,-1,-1,-1"

    for (probY <- problemSetS) {

      totalCountT = totalCountT + 1
      val preParseTime = System.nanoTime

      report.println("Proof " + totalCountT + ": " + probY)
      val proofToTest = ProofParserSPASS.read(probY)
      var variables = ProofParserSPASS.getVars()

      val postParseTime = System.nanoTime

      val proofLength = proofToTest.size
      val numRes = countResolutionNodes(proofToTest)
      val parseTime = postParseTime - preParseTime

      val startTime = System.nanoTime

      val timeout = 1000
      val cottonSplit = new FOCottonSplit(variables, timeout)
      try {
        val compressedProof = cottonSplit(proofToTest)

        val resNodesAfter = countResolutionNodes(compressedProof)
        if (resNodesAfter < numRes) {
          report.println("Proof after split has " + (numRes - resNodesAfter) + " less resolution node(s)")
          report.println(proofToTest)
          report.println(compressedProof)
        } else {
          report.println("The proof was not compressed\n\n")
          //println(compressedProof)
          report.println("\n\n#########################################\n\n")
        }

        report.flush()
      } catch {
        case e: Exception =>
          report.println("Variables: " + variables.mkString(","))
          report.println(proofToTest)
          report.println("There was a problem to resolve the proofs after splitting!\n" + e.toString)
          report.println("\n\n#########################################\n\n")
          report.flush()
      }
    }
        /*
        if (compressedProof.root.conclusion.ant.nonEmpty || compressedProof.root.conclusion.suc.nonEmpty) {
          etempT.println(probY.substring(path.length) + ",0," + proofLength + "," + numRes + noDataString + "-ERROR")
          etempT.flush()
        } else {

          val endTime = System.nanoTime
          val runTime = endTime - startTime
          val compressedLengthAll = compressedProof.size
          val compressedLengthResOnly = countResolutionNodes(compressedProof)

          val compressionRatio = (proofLength - compressedLengthAll) / proofLength.toDouble
          val compressionSpeed = (proofLength - compressedLengthAll) / runTime.toDouble

          val compressionRatioRes = (numRes - compressedLengthResOnly) / proofLength.toDouble
          val compressionSpeedRes = (numRes - compressedLengthResOnly) / runTime.toDouble

          val numSub = countFOSub(compressedProof)

          if (compressionRatioRes < 0) {
            etempT.println(probY.substring(path.length) + ",0," + proofLength + "," + numRes + noDataString)
            etempT.flush()
          } else {

            etempT.println(probY.substring(path.length) + ",1," + proofLength + "," + numRes + "," + compressedLengthAll + ","
              + compressedLengthResOnly + "," + runTime + "," + compressionRatio + "," + compressionSpeed + "," + compressionRatioRes + "," + compressionSpeedRes+","+numSub+","+parseTime)
            etempT.flush()
          }
        }
      } catch {
        case e: CompressionException => {
          val proofToTest = ProofParserSPASS.read(probY)

          val proofLength = proofToTest.size
          val numRes = countResolutionNodes(proofToTest)

          etempT.println(probY.substring(path.length) + ",0," + proofLength + "," + numRes + noDataString)
          etempT.flush()
        }
      }
    }
    println("total: " + totalCountT)
    */
  }
}

/**
  * This class let us generate random proofs to test the algorithm and
  * analyse the cases where it fails.
  *
  */
object FOSplittingReview {
  def main(args : Array[String]) : Unit = {
    val generator = new ProofGenerator(2)
    var proof : Proof[SequentProofNode] = null
    var vars  : collection.mutable.Set[Var] = null
    try {
      while (true) {
        proof = generator.generateProof()
        vars  = generator.getVariables()
        val split = new FOCottonSplit(vars, 1)
        if(proof.size < 10)
          split(proof)
      }
    } catch {
      case e : Exception =>
        println(ProofToTPTPFile(proof))
        println()
        println(proof)
        println()
        println(e)
    }
  }
}

object ProofDebug {
  def main(args : Array[String]) : Unit = {
    val proofTPTP =
      """
        |cnf(c0,axiom,p5(c5) | p3(c3)).
        |cnf(c1,axiom,~p3(c3)).
        |cnf(c2,plain,p5(c5),inference(sr,[status(thm)],[c0,c1])).
        |cnf(c3,axiom,~p5(V1) | p3(V1) | p3(c3)).
        |cnf(c4,plain,~p5(V1) | p3(V1),inference(sr,[status(thm)],[c3,c1])).
        |cnf(c5,plain,p3(c5),inference(sr,[status(thm)],[c2,c4])).
        |cnf(c6,axiom,~p3(c5) | ~p3(V0)).
        |cnf(c7,plain,~p3(c5),inference(cn,[status(thm)],[c6])).
        |cnf(c8,plain,$false,inference(sr,[status(thm)],[c5,c7])).
      """.stripMargin
    val proof = ProofParserCNFTPTP.extractFromString(proofTPTP)
    val vars  = ProofParserCNFTPTP.getVariables
    ProofParserCNFTPTP.resetVariables()
    println(proof)
    try{
      val split = new FOCottonSplit(vars, 1)
      split(proof)
    } catch {
      case e : Exception =>
        println(ProofToTPTPFile(proof))
        println()
        println(proof)
        println()
        println(e)
    }
  }
}

object TestContraction {
  def main(args : Array[String]) : Unit = {
    val sequent = Sequent()(Atom("p1",List(Var("c1",i))),Atom("p1",List(Var("V0",i))))
    println(Contraction.contractIfPossible(Axiom(sequent),MSet[Var](Var("V0",i))))
  }
}