package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.expression._
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }


import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner


@RunWith(classOf[JUnitRunner])
class FORPILUSpecification extends SpecificationWithJUnit with  checkProofEquality  {

  //Variants of Bruno's proof

  val proofa = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1.spass")
  val resulta = checkProofs(FORecyclePivotsWithIntersection(proofa), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1.result")

  //should change
  val proofb = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1b.spass")
  val resultb = checkProofs(FORecyclePivots(proofb), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1b.result")

  //Should not change the proof
  val proofc = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1c.spass")
  val resultc = checkProofs(FORecyclePivots(proofc), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1c.result")

  //Should change the proof
  val proofd = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1d.spass")
  val resultd = checkProofs(FORecyclePivots(proofd), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1d.result")

  //Should change the proof
  val proofe = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1e.spass")
  val resulte = checkProofs(FORecyclePivots(proofe), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1e.result")

  //Should change the proof
  val prooff = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1f.spass")
  val resultf = checkProofs(FORecyclePivots(prooff), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1f.result")

  //should not change
  val proofg = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1g.spass")
  val resultg = checkProofs(FORecyclePivots(proofg), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1g.result")

  //Should not change the proof -- MRR test
  val proofh = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1h.spass")
  val resulth = checkProofs(FORecyclePivots(proofh), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample1h.result")

  //Example from the video, trivially made first-order
  //basic
  val proof2a = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2.spass")
  val result2a = checkProofs(FORecyclePivotsWithIntersection(proof2a), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2.result")

  //tests if 'more general' idea works in intersection
  val proof2b = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2b.spass")
  val result2b = checkProofs(FORecyclePivotsWithIntersection(proof2b), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2b.result")

  //should not change the proof; checks 'more general' idea in intersection
  val proof2c = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2c.spass")
  val result2c = checkProofs(FORecyclePivotsWithIntersection(proof2c), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2c.result")

  //tests intersection; should not compress
  val proof2d = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2d.spass")
  val result2d = checkProofs(FORecyclePivotsWithIntersection(proof2d), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2d.result")
  
  //tests intersection; should not compress
//  val proof2e = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample2e.spass")
//  val proof2eResult = FORecyclePivotsWithIntersection(proof2e)
//  print(proof2eResult)
  //val result2e = checkProofs(FORecyclePivotsWithIntersection(proof2d), "examples/proofs/SPASS/testresults/FORPILU/FORPIexample2d.result")

  
  //August 9th 2016 Examples
  
     val proofA9a = ProofParserSPASS.read("examples/proofs/SPASS/FORPIExamples/e1.spass")   
//     println("Proof parsed.")
//     println(proofA9a)
     val cproofA9 = FORecyclePivotsWithIntersection(proofA9a)
//     println("A9A: ")
//     println(cproofA9)
     val resultA9a = checkProofs(cproofA9, "examples/proofs/SPASS/testresults/FORPILU/e1r.spass")     
     
     val proofA9b = ProofParserSPASS.read("examples/proofs/SPASS/FORPIExamples/e2.spass")   
//     println("Proof parsed.")
//     println(proofA9b)
     val cproofA9b = FORecyclePivotsWithIntersection(proofA9b)
//     println("A9B: ")
//     println(cproofA9b)   
     val resultA9b = checkProofs(cproofA9b, "examples/proofs/SPASS/testresults/FORPILU/e2r.spass")     
     
     
     
     val proofA9c = ProofParserSPASS.read("examples/proofs/SPASS/FORPIExamples/e3.spass")   
//     println("Proof parsed.")
//     println(proofA9c)
     val cproofA9c = FORecyclePivotsWithIntersection(proofA9c)
//     println("A9C: ")
//     println(cproofA9c)    
     val resultA9c = checkProofs(cproofA9c, "examples/proofs/SPASS/testresults/FORPILU/e3r.spass")     
  
  
  //For debugging:
//
//     println("-----FROM HERE")
//     try{
//  
//     val proofA9a = ProofParserSPASS.read("examples/proofs/SPASS/FORPIExamples/e1.spass")   
////     println("Proof parsed.")
////     println(proofA9a)
//     val cproofA9 = FORecyclePivotsWithIntersection(proofA9a) 
//     val resultA9a = checkProofs(cproofA9, "examples/proofs/SPASS/testresults/FORPILU/e1r.spass") 
//     } catch {
//       case e: Exception => {
//         println("error")
//         e.printStackTrace()
//       }
//     }

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
    
    //August 9th 2016 Tests:
    "Compress a small example correctly - no null pointer" in {
      resultA9a must beEqualTo(true)
    }
    "Compress a small example correctly - no scala.MatchError" in {
      resultA9b must beEqualTo(true)
    }
    "Compress a small example correctly - no scala.MatchError (2)" in {
      resultA9c must beEqualTo(true)
    }    
  }
}