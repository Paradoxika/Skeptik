package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class FOLowerUnitsSpecification extends SpecificationWithJUnit {

  val proofa = ProofParserSPASS.read("examples/proofs/SPASS/example1.spass")
  val computeda = FOLowerUnits(proofa).toString
  val expecteda = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example1.result").mkString

  val proofb = ProofParserSPASS.read("examples/proofs/SPASS/example3.spass")
  val computedb = FOLowerUnits(proofb).toString
  val expectedb = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example3.result").mkString

  val proofq = ProofParserSPASS.read("examples/proofs/SPASS/example4q.spass")
  val computedq = FOLowerUnits(proofq).toString
  val expectedq = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example4q.result").mkString

  "FOLowerUnits" should {
    "Compress the first proof correctly" in {
      computeda.trim must beEqualTo(expecteda.trim)
    }
    "Compress the second proof correctly" in {
      computedb.trim must beEqualTo(expectedb.trim)
    }
    "Compress the third proof correctly" in {
      computedq.trim must beEqualTo(expectedq.trim)
    }
  }
}