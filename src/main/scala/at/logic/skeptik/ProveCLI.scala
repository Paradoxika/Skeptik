package at.logic.skeptik

import at.logic.skeptik.algorithm.prover.structure.immutable.CNF
import at.logic.skeptik.algorithm.prover.{CNFProblemParser, CR, ConcurrentCR}
import at.logic.skeptik.expression.{Abs, App, E, Var}
import at.logic.skeptik.util.io.{Output, StandardOutput}

import scala.collection.mutable

/**
  * @author Daniyar Itegulov
  */
object ProveCLI {

  case class Config(inputs: Seq[String] = Seq(),
                    algorithm: String = "CR",
                    format: Option[String] = None,
                    output: Output = StandardOutput)

  val algorithms = Map(
    "CR" -> CR,
    "ConcurrentCR" -> ConcurrentCR
  )
  val parsers = Map(
    "cnf" -> CNFProblemParser,
    "cnfp" -> CNFProblemParser
  )
  val knownFormats = Seq("cnf", "cnfp")

  val parser = new scopt.OptionParser[Config]("skeptik-prove") {
    head("\nSkeptik's Command Line Interface for Proof generation\n\n")

    opt[String]('a', "algorithm") unbounded() action { (v, c) =>
      c.copy(algorithm = v)
    } text "use <alg> to generate proof" valueName "<alg>"

    note(
      s"""
        <alg> can be any of the following algorithms:
        ${algorithms.keys}
        """
    )

    opt[String]('f', "format") action { (v, c) =>
      c.copy(format = Some(v))
    } validate { v =>
      if (knownFormats contains v) success
      else failure("unknown problem format: " + v)
    } text s"use <format> (either $knownFormats) for input problem\n" valueName "<format>"

    opt[String]('o', "out") action { (v, c) =>
      c.copy(output = Output(v))
    } text "output proof to <file>\n" valueName "<file>"

    arg[String]("<problem-file>...") unbounded() optional() action { (v, c) =>
      c.copy(inputs = c.inputs :+ v)
    } text "generate proof for <problem-file>\n"

    note(
      """
    Example:
      The following command solve the problem 'SET006-1.cnfp' using the
      algorithm 'ConcurrentCR'.
      The output proof is written to 'proof.out'.

      skeptik-prove -a ConcurrentCR -f cnfp -o proof.out examples/problems/CNF/SET006-1.cnfp
      """)
  }

  def getUppercaseVariables(cnf: CNF): mutable.Set[Var] = {
    def uppercaseVariableInFormula(e: E): Set[Var] = e match {
      case v: Var if v.name.charAt(0).isUpper => Set(v)
      case App(l, r) => uppercaseVariableInFormula(l) ++ uppercaseVariableInFormula(r)
      case Abs(_, body) => uppercaseVariableInFormula(body)
      case _ => Set()
    }
    val variables = mutable.Set.empty[Var]
    cnf.clauses.flatMap(clause => clause.ant ++ clause.suc).foreach(variables ++= uppercaseVariableInFormula(_))
    variables
  }

  def main(args: Array[String]): Unit = {
    parser.parse(args, Config()) foreach { c =>
      val algorithm = algorithms(c.algorithm)
      for (input <- c.inputs) {
        val problemParser = parsers(c.format.getOrElse(input.split(".").last))
        val cnf = problemParser.parse(input)
        implicit val variables = getUppercaseVariables(cnf)
        println("Unification variables are: " + variables)
        c.output.write(algorithm.prove(cnf).getOrElse("Satisfiable"))
      }
    }
  }
}
