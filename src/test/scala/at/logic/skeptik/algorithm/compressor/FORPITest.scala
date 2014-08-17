package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class FORPILUSpecification extends SpecificationWithJUnit {

  //Variants of Bruno's proof
  
  val proofa = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1.spass")
  val resulta = FORecyclePivotsWithIntersection(proofa).toString
  val expecteda = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample1.result").mkString

  //should change
  val proofb = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1b.spass")
  val resultb = FORecyclePivots(proofb).toString
  val expectedb = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample1b.result").mkString

  //Should not change the proof
  val proofc = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1c.spass")
  val resultc = FORecyclePivots(proofc).toString
  val expectedc = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample1c.result").mkString

  //Should change the proof
  val proofd = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1d.spass")
  val resultd = FORecyclePivots(proofd).toString
  val expectedd = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample1d.result").mkString

  //Should change the proof
  val proofe = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1e.spass")
  val resulte = FORecyclePivots(proofe).toString
  val expectede = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample1e.result").mkString

  //Should not change the proof
  val prooff = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1f.spass")
  val resultf = FORecyclePivots(prooff).toString
  val expectedf = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample1f.result").mkString

  //should not change
  val proofg = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1g.spass")
  val resultg = FORecyclePivots(proofg).toString
  val expectedg = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample1g.result").mkString

  //Should not change the proof -- MRR test
  val proofh = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1h.spass")
  val resulth = FORecyclePivots(proofh).toString
  val expectedh = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample1h.result").mkString

  //Example from the video, trivially made first-order
  val proof2a = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2.spass")
  val result2a = FORecyclePivotsWithIntersection(proof2a).toString
  val expected2a = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FORPILU/FORPIexample2.result").mkString
  
  //TODO: add another example that tests intersection where a pivot is not shared (but similar)    

  //TODO: give these meaninful names
  "FORPILU" should {
    "Compress the proof correctly (small compression)" in {
      resulta.trim must beEqualTo(expecteda.trim)
    }
    "Parse the proof correctly" in {
      resultb.trim must beEqualTo(expectedb.trim)
    }
    "Parse the proof correctly" in {
      resultc.trim must beEqualTo(expectedc.trim)
    }
    "Parse the proof correctly" in {
      resultd.trim must beEqualTo(expectedd.trim)
    }
    "Parse the proof correctly" in {
      resulte.trim must beEqualTo(expectede.trim)
    }
    "Parse the proof correctly" in {
      resultf.trim must beEqualTo(expectedf.trim)
    }
    "Parse the proof correctly" in {
      resultg.trim must beEqualTo(expectedg.trim)
    }
    "Parse the proof correctly" in {
      resulth.trim must beEqualTo(expectedh.trim)
    }
    "Handle intersection (and contractions) correctly" in {
      result2a.trim must beEqualTo(expected2a.trim)
    }
  }
}