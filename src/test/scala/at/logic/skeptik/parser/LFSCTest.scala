package at.logic.skeptik.parser


import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class ProofParserLFSCSpecification extends SpecificationWithJUnit {

    val proof = ProofParserLFSC.read("examples/proofs/LFSC/short.lfsc")
    val computed = proof.toString
    val expected = scala.io.Source.fromFile("examples/proofs/LFSC/testresults/short.result").mkString

  
  "ProofParserLFSC" should {
    "Parse the proof correctly" in {
      computed.trim must beEqualTo(expected.trim)
    }

  }
}
