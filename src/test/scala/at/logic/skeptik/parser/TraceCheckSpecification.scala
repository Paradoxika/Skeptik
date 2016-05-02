package at.logic.skeptik.parser

import at.logic.skeptik.algorithm.compressor.DAGify
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TraceCheckSpecification extends SpecificationWithJUnit {

    val proof = ProofParserTraceCheck.read("examples/proofs/TraceCheck/dubois50.tc")
    "TraceCheck parsed proof " should {
      "be dagified " in {
        proof.size == DAGify(proof).size
      }
    }
//  }
}