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

  val proofb = ProofParserSPASS.read("examples/proofs/SPASS/example2.spass")
  val computedb = FOLowerUnits(proofb).toString
  //println(computedb)
  val expectedb = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example2.result").mkString

  val proofc = ProofParserSPASS.read("examples/proofs/SPASS/example3.spass")
  val computedc = FOLowerUnits(proofc).toString
  val expectedc = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example3.result").mkString

  val proofd = ProofParserSPASS.read("examples/proofs/SPASS/example4q.spass")
  val computedd = FOLowerUnits(proofd).toString
  val expectedd = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example4q.result").mkString

  //5: some specific variables
  val proofe = ProofParserSPASS.read("examples/proofs/SPASS/example5.spass")
  val computede = FOLowerUnits(proofe).toString
  val expectede = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example5.result").mkString

  //6: mix of universal/non-universal 
  val prooff = ProofParserSPASS.read("examples/proofs/SPASS/example6.spass")
  val computedf = FOLowerUnits(prooff).toString
  val expectedf = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example6.result").mkString

  //7: unit is resolved against several nodes, but still lowered correctly:
  val proofg = ProofParserSPASS.read("examples/proofs/SPASS/example7.spass")
  val computedg = FOLowerUnits(proofg).toString
  val expectedg = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example7.result").mkString

  //8: unit can't be lowered
  val proofh = ProofParserSPASS.read("examples/proofs/SPASS/example8.spass")
  val computedh = FOLowerUnits(proofh).toString
  val expectedh = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example8.result").mkString  
  
  //9: the unit is the relativley least general form 
  val proofi = ProofParserSPASS.read("examples/proofs/SPASS/example9.spass")
  val computedi = FOLowerUnits(proofi).toString
  val expectedi = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example9.result").mkString    
  
  "FOLowerUnits" should {
    "Compress the first proof correctly (example proof; no MRR required)" in {
      computeda.trim must beEqualTo(expecteda.trim)
    }
    "Compress the second proof correctly (when lowering requires a non-unit resolution)" in {
      computedb.trim must beEqualTo(expectedb.trim)
    }
    "Compress the third proof correctly (MRR required)" in {
      computedc.trim must beEqualTo(expectedc.trim)
    }
    "Compress the fourth proof correctly (larger; MRR required)" in {
      computedd.trim must beEqualTo(expectedd.trim)
    }
    "Compress the fifth proof correctly (all specific variables)" in {
      computede.trim must beEqualTo(expectede.trim)
    }
    "Compress the sixth proof correctly (not all universal variables)" in {
      computedf.trim must beEqualTo(expectedf.trim)
    }    
    "Compress the seventh proof correctly (unit resolved against several clauses; lowered)" in {
      computedg.trim must beEqualTo(expectedg.trim)
    }     
    "Compress the eigth proof correctly (unit cannot be lowered)" in {
      computedh.trim must beEqualTo(expectedh.trim)
    }   
    "Compress the ninth proof correctly (unit is relatively least general)" in {
      computedi.trim must beEqualTo(expectedi.trim)
    }       
  }
}