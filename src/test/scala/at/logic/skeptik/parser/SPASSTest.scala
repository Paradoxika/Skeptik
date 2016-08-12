package at.logic.skeptik.parser

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class ProofParserSPASSSpecification extends SpecificationWithJUnit {

  val proof1 = ProofParserSPASS.read("examples/proofs/SPASS/completespaceforn_5.spass")
  val computed1 = proof1.toString
  val expected1 = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/ProofParserSPASS/completespaceforn_5.result").mkString
  
  val proof2 = ProofParserSPASS.read("examples/proofs/SPASS/FSTP2.spass")
  val computed2 = proof2.toString
  val expected2 = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/ProofParserSPASS/FSTP2.result").mkString

  val proof3 = ProofParserSPASS.read("examples/proofs/SPASS/example2.spass")
  val computed3 = proof3.toString
  val expected3 = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/ProofParserSPASS/example2.result").mkString

  val proof4 = ProofParserSPASS.read("examples/proofs/SPASS/example1.spass")
  val computed4 = proof4.toString
  val expected4 = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/ProofParserSPASS/example1.result").mkString

  "ProofParserSPASS" should {
    "Parse the first proof correctly" in {
      computed1.trim must beEqualTo(expected1.trim)
    }
    "Parse the second proof correctly" in {
      computed2.trim must beEqualTo(expected2.trim)
    }
    "Parse the third proof correctly" in {
      computed3.trim must beEqualTo(expected3.trim)
    }
    "Parse the fourth proof correctly" in {
      computed4.trim must beEqualTo(expected4.trim)
    }
  }
}
