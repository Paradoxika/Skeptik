package at.logic.skeptik.algorithm.FOProofsGenerator

import java.io.PrintWriter

import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.term.FunctionTerm
import at.logic.skeptik.expression.{App, E, Var}
import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import collection.mutable.{Set => MSet}
import scala.io.Source


/**
  * The object RandomProofsTest show results related to proofs randombly generated
  */
object RandomProofsTest {

  def generateProof(proofHeight : Int) : (Proof[Node],MSet[Var]) = {
    val generator = new ProofGenerator(proofHeight)
    try {
      (generator.generateProof(),generator.getVariables())
    } catch {
      case e : Exception =>
        generateProof(proofHeight)
    }
  }

  import ProofsDataRecollection._

  def main(args : Array[String]) : Unit = {

    val report = new PrintWriter("proofsData.log")
    report.println("Size,Height,Axioms,Contractions,Resolutions,Predicates,Functions,Constants,Variables")
    report.flush()

    val numberOfProofs : Int = 68
    val data : Array[ProofData] = new Array[ProofData](numberOfProofs)

    var next = 0
    for (i <- 1 to numberOfProofs) {
      val (proof,vars) : (Proof[Node],MSet[Var]) = generateProof(4)
      val proofData    : ProofData               = numberOf(proof,vars)
      proofData.setHeight(proofHeight(proof))
      report.println(format(proofData.size)+ ", " + format(proofData.height) + ", " + proofData.toString)
      report.flush()
      data(next) = proofData
      next += 1
    }

    val heights      : Array[Double] = new Array[Double](numberOfProofs)
    val axioms       : Array[Double] = new Array[Double](numberOfProofs)
    val resolutions  : Array[Double] = new Array[Double](numberOfProofs)
    val contractions : Array[Double] = new Array[Double](numberOfProofs)
    for(i <- 0 until numberOfProofs){
      heights(i)      = (data(i).height * 1.0) / data(i).size
      axioms(i)       = (data(i).numberOfAxioms * 1.0)/data(i).size
      resolutions(i)  = (data(i).numberOfResolutions * 1.0)/data(i).size
      contractions(i) = (data(i).numberOfContractions * 1.0)/data(i).size
    }

    var averageSize         = 0.0
    var averageHeight       = 0.0
    var averageAxioms       = 0.0
    var averageResolutions  = 0.0
    var averageContractions = 0.0
    for(i <- 0 until numberOfProofs) {
      println(data(i).size + " , " + heights(i) + " , " + axioms(i) + " , " + contractions(i) + " , " + resolutions(i))
      averageSize         += data(i).size
      averageHeight       += heights(i)
      averageAxioms       += axioms(i)
      averageResolutions  += resolutions(i)
      averageContractions += contractions(i)
    }
    averageSize         /= numberOfProofs
    averageHeight       /= numberOfProofs
    averageAxioms       /= numberOfProofs
    averageResolutions  /= numberOfProofs
    averageContractions /= numberOfProofs
    println("Averages")
    println(averageSize + " , " + averageHeight + " , " + averageAxioms + " , " + averageContractions + " , " + averageResolutions)
  }
}

/**
  * The object FilesTests show results related to real proofs collected from SPASS
  */

object FilesTests {

  import ProofsDataRecollection._

  def main(args : Array[String]) : Unit = {
    val path      : String = "/home/eze/Escritorio/Skeptik/GoodProofs/ALL/"
    val proofList : String = "/home/eze/Escritorio/Skeptik/GoodProofs/ALL/list.txt"

    val problemSetS = getProblems(proofList, path)

    val report = new PrintWriter("proofsData.log")
    report.println("Size,Height,Axioms,Contractions,Resolutions,Predicates,Functions,Constants,Variables")
    report.flush()

    val numberOfProofs : Int = 68
    val data : Array[ProofData] = new Array[ProofData](numberOfProofs)

    var totalCountT : Int = 0
    var next = 0
    for (probY <- problemSetS) {
      totalCountT = totalCountT + 1
      println("Proof " + totalCountT + ": " + probY)
      val proof     : Proof[Node] = ProofParserSPASS.read(probY)
      val vars      : MSet[Var]   = ProofParserSPASS.getVars()
      val proofData : ProofData   = numberOf(proof,vars)
      proofData.setHeight(proofHeight(proof))
      report.println(format(proofData.size)+ ", " + format(proofData.height) + ", " + proofData.toString)
      report.flush()
      if(proofData.size >= 20) {
        data(next) = proofData
        next += 1
      }
    }

    val heights      : Array[Double] = new Array[Double](numberOfProofs)
    val axioms       : Array[Double] = new Array[Double](numberOfProofs)
    val resolutions  : Array[Double] = new Array[Double](numberOfProofs)
    val contractions : Array[Double] = new Array[Double](numberOfProofs)
    for(i <- 0 until numberOfProofs){
      heights(i)      = (data(i).height * 1.0) / data(i).size
      axioms(i)       = (data(i).numberOfAxioms * 1.0)/data(i).size
      resolutions(i)  = (data(i).numberOfResolutions * 1.0)/data(i).size
      contractions(i) = (data(i).numberOfContractions * 1.0)/data(i).size
    }

    var averageSize         = 0.0
    var averageHeight       = 0.0
    var averageAxioms       = 0.0
    var averageResolutions  = 0.0
    var averageContractions = 0.0
    for(i <- 0 until numberOfProofs) {
      println(data(i).size + " , " + heights(i) + " , " + axioms(i) + " , " + contractions(i) + " , " + resolutions(i))
      averageSize         += data(i).size
      averageHeight       += heights(i)
      averageAxioms       += axioms(i)
      averageResolutions  += resolutions(i)
      averageContractions += contractions(i)
    }
    averageSize         /= numberOfProofs
    averageHeight       /= numberOfProofs
    averageAxioms       /= numberOfProofs
    averageResolutions  /= numberOfProofs
    averageContractions /= numberOfProofs
    println("Avarages")
    println(averageSize + " , " + averageHeight + " , " + averageAxioms + " , " + averageContractions + " , " + averageResolutions)
  }
}

/**
  * Here we will implement methods to explore the parameters of proofs such as
  * number of variables, constants, predicates, functions, proof's height and
  * proof's size.
  */
object ProofsDataRecollection {

  def format(x : Int) : String =
    if(x < 10) " " + x.toString
    else x.toString

  def getProblems(file: String, path: String): MSet[String] = {
    val outTj = MSet[String]()

    for (line <- Source.fromFile(file).getLines()) {
      val newProblemN = path + line
      println(newProblemN)
      outTj.add(newProblemN)
    }
    outTj
  }




  def proofHeight(p : Proof[Node]) : Int = {
    def nodeHeight(node : Node) : Int =
      node match {
        case Axiom(_)                                         => 1
        case Contraction(premise,_)                           => 1 + nodeHeight(premise)
        case UnifyingResolution(leftPremise,rightPremise,_,_) => 1 + math.max(nodeHeight(leftPremise),nodeHeight(rightPremise))
      }
    nodeHeight(p.root)
  }


  def numberOf(proof : Proof[Node], vars : MSet[Var]) : ProofData = {
    var axioms       = MSet[Node]()
    var resolutions  = MSet[Node]()
    var contractions = MSet[Node]()

    val variables  = MSet[Var]()
    val constants  = MSet[String]()
    val functions  = MSet[String]()
    val predicates = MSet[String]()

    def exploreNode(node: Node): Unit =
      node match {
        case Axiom(sequent) =>
          axioms += node
          exploreSequent(sequent)
        case Contraction(premise, desired) =>
          contractions += node
          exploreSequent(desired)
          exploreNode(premise)
        case UnifyingResolution(leftPremise, rightPremise, _, _) =>
          resolutions += node
          exploreNode(leftPremise)
          exploreNode(rightPremise)
          val sequent = UnifyingResolution.resolve(leftPremise, rightPremise, vars)
          exploreSequent(sequent.conclusion)
      }

    def exploreSequent(sequent: Sequent): Unit = {
      sequent.ant foreach exploreLiteral
      sequent.suc foreach exploreLiteral
    }

    def exploreLiteral(literal: E): Unit =
      literal match {
        case Atom(Var(name, _), args) =>
          predicates += name
          args foreach exploreTerm
        case App(predicate, argument) =>
          exploreLiteral(predicate)
          exploreTerm(argument)
        case Var(name, _) => predicates += name
      }

    def exploreTerm(term: E): Unit = {
      def isVariable(name: String): Boolean = name.charAt(0).isUpper
      term match {
        case v@Var(name, _) =>
          if (isVariable(name)) variables += v
          else constants += name
        case FunctionTerm(Var(name, _), args) =>
          functions += name
          args foreach exploreLiteral
      }
    }

    exploreNode(proof.root)
    new ProofData(axioms.size, contractions.size, resolutions.size,
      predicates.size, functions.size, constants.size,variables.size)
  }
}

class ProofData(val numberOfAxioms : Int, val numberOfContractions : Int, val numberOfResolutions : Int,
                val numberOfPredicates : Int, val numberOfFunctions : Int, val numberOfConstants : Int,
                val numberOfVariables : Int) {

  val size = numberOfResolutions + numberOfContractions + numberOfAxioms
  private var proofHeight : Int = 0
  def setHeight(h : Int) : Unit =
    proofHeight = h
  def height : Int = proofHeight

  private def format(x : Int) : String =
    if(x < 10) " " + x.toString
    else x.toString

  override def toString :String =
    format(numberOfAxioms) + ", " + format(numberOfContractions) + ", " + format(numberOfResolutions) + ", " +
      format(numberOfPredicates) + ", " + format(numberOfFunctions) + ", " + format(numberOfConstants) + ", " +
        format(numberOfVariables)
}
