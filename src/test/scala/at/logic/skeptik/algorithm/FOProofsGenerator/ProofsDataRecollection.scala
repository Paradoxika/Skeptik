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

import collection.mutable.{HashSet, Set => MSet}
import scala.io.Source

/**
  * Here we will explore the parameters of real proofs such as
  * number of variables, constants, predicates, functions, proof's height
  * and proof's size.
  */
object ProofsDataRecollection {

  private def format(x : Int) : String =
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

  def main(args : Array[String]) : Unit = {
    val path      : String = "/home/eze/Escritorio/Skeptik/GoodProofs/ALL/"
    val proofList : String = "/home/eze/Escritorio/Skeptik/GoodProofs/ALL/list.txt"

    val problemSetS = getProblems(proofList, path)

    val report = new PrintWriter("proofsData.log")
    report.println("Size,Height,Axioms,Contractions,Resolutions,Predicates,Functions,Constants,Variables")
    report.flush()

    var totalCountT : Int = 0
    for (probY <- problemSetS) {
      totalCountT = totalCountT + 1
      println("Proof " + totalCountT + ": " + probY)
      val proof     : Proof[Node] = ProofParserSPASS.read(probY)
      val vars      : MSet[Var]   = ProofParserSPASS.getVars()
      val proofData : ProofData   = numberOf(proof,vars)
      report.println(format(proof.size)+ ", " + format(proofHeight(proof)) + ", " + proofData.toString)
      report.flush()
    }
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

  private def format(x : Int) : String =
    if(x < 10) " " + x.toString
    else x.toString

  override def toString :String =
    format(numberOfAxioms) + ", " + format(numberOfContractions) + ", " + format(numberOfResolutions) + ", " +
      format(numberOfPredicates) + ", " + format(numberOfFunctions) + ", " + format(numberOfConstants) + ", " +
        format(numberOfVariables)
}