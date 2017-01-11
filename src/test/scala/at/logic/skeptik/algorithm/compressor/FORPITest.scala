package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class FORPILUSpecification extends SpecificationWithJUnit with checkProofEquality {

  //Variants of Bruno's proof
  println("Begging FORPI test..")
  
  val proofa = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1.spass")
  val resulta = checkProofs(FORecyclePivotsWithIntersection(proofa), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1.result")
  println("FORPI Test: a completed")
  //should change
  val proofb = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1b.spass")
  val resultb = checkProofs(FORecyclePivots(proofb), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1b.result")
println("FORPI Test: b completed")

  //Should not change the proof
  val proofc = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1c.spass")
  val resultc = checkProofs(FORecyclePivots(proofc), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1c.result")
println("FORPI Test: c completed")

  //Should change the proof
  val proofd = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1d.spass")
  val resultd = checkProofs(FORecyclePivots(proofd), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1d.result")
println("FORPI Test: d completed")

  //Should change the proof
  val proofe = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1e.spass")
  val resulte = checkProofs(FORecyclePivots(proofe), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1e.result")
println("FORPI Test: e completed")

  //Should change the proof
  val prooff = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1f.spass")
  val resultf = checkProofs(FORecyclePivots(prooff), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1f.result")
println("FORPI Test: f completed")

  //should not change
  val proofg = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1g.spass")
  val resultg = checkProofs(FORecyclePivots(proofg), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1g.result")
println("FORPI Test: g completed")

  //Should not change the proof -- MRR test
  val proofh = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1h.spass")
  val resulth = checkProofs(FORecyclePivots(proofh), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1h.result")
println("FORPI Test: h completed")

  //Example from the video, trivially made first-order
  //basic
  val proof2a = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2.spass")
  val result2a = checkProofs(FORecyclePivotsWithIntersection(proof2a), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2.result")
println("FORPI Test: 2a completed")

  //tests if 'more general' idea works in intersection
  val proof2b = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2b.spass")
  val result2b = checkProofs(FORecyclePivotsWithIntersection(proof2b), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2b.result")
println("FORPI Test: 2b completed")

  //should not change the proof; checks 'more general' idea in intersection
  val proof2c = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2c.spass")
  val result2c = checkProofs(FORecyclePivotsWithIntersection(proof2c), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2c.result")
println("FORPI Test: 2c completed")

  //tests intersection; should not compress
  val proof2d = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2d.spass")
  val result2d = checkProofs(FORecyclePivotsWithIntersection(proof2d), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2d.result")
println("FORPI Test: 2d completed")

  println("-----")
  println("input proof: \n" + proofa)
  println("-----")
  println("Testing proof: \n" + FORecyclePivotsWithIntersection(proofa))
  
  "FORPILU" should {
    "Compress the proof correctly (small compression)" in {
      resulta must beEqualTo(true)
    }
    "Compress the proof correctly (all universal variables)" in {
      resultb must beEqualTo(true)
    }
    "Not change a proof if it can't be compressed" in {
      resultc must beEqualTo(true)
    }
    "Compress correctly with one specific variables" in {
      resultd must beEqualTo(true)
    }
    "Compress correctly with one specific variables (spread out)" in {
      resulte must beEqualTo(true)
    }
    "Compress when the exact form of the literal is found" in {
      resultf must beEqualTo(true)
    }
    "Not change a proof if it can't be compressed (specific variables)" in {
      resultg must beEqualTo(true)
    }
    "Work with MRR nodes" in {
      resulth must beEqualTo(true)
    }
    "Handle intersection (and contractions) correctly" in {
      result2a must beEqualTo(true)
    }
    "Should interpret 'more general' literals correctly when using intersection" in {
      result2b must beEqualTo(true)
    }
    "Detect when a proof cannot be compressed" in {
      result2c must beEqualTo(true)
    }
    "Compute the intersection correctly" in {
      result2d must beEqualTo(true)
    }
  }
}