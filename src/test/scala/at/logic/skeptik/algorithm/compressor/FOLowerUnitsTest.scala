package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.parser.SequentParser
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.Contraction
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import collection.mutable.{ HashMap => MMap, Set => MSet }
import at.logic.skeptik.expression._

@RunWith(classOf[JUnitRunner])
class FOLowerUnitsSpecification extends SpecificationWithJUnit with checkProofEquality {

  val proofa = ProofParserSPASS.read("examples/proofs/SPASS/example1.spass")
  val resulta = checkProofs(FOLowerUnits(proofa), "examples/proofs/SPASS/testresults/FOLowerUnits/example1.result")

  val proofb = ProofParserSPASS.read("examples/proofs/SPASS/example2.spass")
  val resultb = checkProofs(FOLowerUnits(proofb), "examples/proofs/SPASS/testresults/FOLowerUnits/example2.result")

  val proofc = ProofParserSPASS.read("examples/proofs/SPASS/example3.spass")
  val resultc = checkProofs(FOLowerUnits(proofc), "examples/proofs/SPASS/testresults/FOLowerUnits/example3.result")

  val proofd = ProofParserSPASS.read("examples/proofs/SPASS/example4q.spass")
  val resultd = checkProofs(FOLowerUnits(proofd), "examples/proofs/SPASS/testresults/FOLowerUnits/example4q.result")

  //5: some specific variables
  val proofe = ProofParserSPASS.read("examples/proofs/SPASS/example5.spass")
  val resulte = checkProofs(FOLowerUnits(proofe), "examples/proofs/SPASS/testresults/FOLowerUnits/example5.result")

  //6: mix of universal/non-universal 
  val prooff = ProofParserSPASS.read("examples/proofs/SPASS/example6.spass")
  val resultf = checkProofs(FOLowerUnits(prooff), "examples/proofs/SPASS/testresults/FOLowerUnits/example6.result")

  //7: unit is resolved against several nodes, but still lowered correctly:
  val proofg = ProofParserSPASS.read("examples/proofs/SPASS/example7.spass")
  val resultg = checkProofs(FOLowerUnits(proofg), "examples/proofs/SPASS/testresults/FOLowerUnits/example7.result")

  //8: unit can't be lowered
  val proofh = ProofParserSPASS.read("examples/proofs/SPASS/example8.spass")
  val resulth = checkProofs(FOLowerUnits(proofh), "examples/proofs/SPASS/testresults/FOLowerUnits/example8.result")

  //9: the unit is the relativley least general form 
  val proofi = ProofParserSPASS.read("examples/proofs/SPASS/example9.spass")
  val resulti = checkProofs(FOLowerUnits(proofi), "examples/proofs/SPASS/testresults/FOLowerUnits/example9.result")

  "FOLowerUnits" should {
    "Compress the first proof correctly (example proof; no MRR required)" in {
      resulta must beEqualTo(true)
    }
    "Compress the second proof correctly (when lowering requires a non-unit resolution)" in {
      resultb must beEqualTo(true)
    }
    "Compress the third proof correctly (MRR required)" in {
      resultc must beEqualTo(true)
    }
    "Compress the fourth proof correctly (larger; MRR required)" in {
      resultd must beEqualTo(true)
    }
    "Compress the fifth proof correctly (all specific variables)" in {
      resulte must beEqualTo(true)
    }
    "Compress the sixth proof correctly (not all universal variables)" in {
      resultf must beEqualTo(true)
    }
    "Compress the seventh proof correctly (unit resolved against several clauses; lowered)" in {
      resultg must beEqualTo(true)
    }
    "Compress the eigth proof correctly (unit cannot be lowered)" in {
      resulth must beEqualTo(true)
    }
    "Compress the ninth proof correctly (unit is relatively least general)" in {
      resulti must beEqualTo(true)
    }
  }
}

trait checkProofEquality extends FindDesiredSequent {
  def checkProofs(p: Proof[SequentProofNode], s: String): Boolean = {

    val proofNodes = p.nodes;
    val proofNodesReversed = proofNodes.reverse

    val input = scala.io.Source.fromFile(s)
    val lines = input.getLines

    val sequents = for (l <- lines) yield SequentParser(l)
    val traversableSequents = sequents.toTraversable

    if (proofNodesReversed.size != traversableSequents.size) {
      return false
    }

    checkSequents(proofNodesReversed, traversableSequents)
  }

  def checkSequents(nodes: Seq[SequentProofNode], seqs: Traversable[Sequent]): Boolean = {
    if (nodes.length == 0) {
      return true
    }

    val vars =
      getSetOfVars(nodes.head) union getSetOfVars(seqs.head.ant: _*) union getSetOfVars(seqs.head.suc: _*)

    if (desiredFound(nodes.head.conclusion, seqs.head)(vars)) {
      return checkSequents(nodes.tail, seqs.tail)
    } else {
      false
    }
  }
}