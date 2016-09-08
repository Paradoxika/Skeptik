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
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import at.logic.skeptik.expression._

@RunWith(classOf[JUnitRunner])
class FOLowerUnitsSpecification extends SpecificationWithJUnit with checkProofEquality {


  val proofa = ProofParserSPASS.read("examples/proofs/SPASS/example1.spass")
  println("FINALA: \n " + FOLowerUnits(proofa))  
  val resulta = checkProofs(FOLowerUnits(proofa), "examples/proofs/SPASS/testresults/FOLowerUnits/example1.result")
  
  val proofb = ProofParserSPASS.read("examples/proofs/SPASS/example2.spass")
  println("FINALB: \n " + FOLowerUnits(proofb))
  val resultb = checkProofs(FOLowerUnits(proofb), "examples/proofs/SPASS/testresults/FOLowerUnits/example2.result")

  val proofc = ProofParserSPASS.read("examples/proofs/SPASS/example3.spass")
  println("FINALC: \n " + FOLowerUnits(proofc))
  val resultc = checkProofs(FOLowerUnits(proofc), "examples/proofs/SPASS/testresults/FOLowerUnits/example3.result")

  val proofd = ProofParserSPASS.read("examples/proofs/SPASS/example4q.spass")
  println("FINALD: \n " + FOLowerUnits(proofd))
  val resultd = checkProofs(FOLowerUnits(proofd), "examples/proofs/SPASS/testresults/FOLowerUnits/example4q.result")

  //5: some specific variables
  val proofe = ProofParserSPASS.read("examples/proofs/SPASS/example5.spass")
  println("FINALE: \n " + FOLowerUnits(proofe))
  val resulte = checkProofs(FOLowerUnits(proofe), "examples/proofs/SPASS/testresults/FOLowerUnits/example5.result")

  //6: mix of universal/non-universal 
  val prooff = ProofParserSPASS.read("examples/proofs/SPASS/example6.spass")
  println("FINALF: \n " + FOLowerUnits(prooff))
  val resultf = checkProofs(FOLowerUnits(prooff), "examples/proofs/SPASS/testresults/FOLowerUnits/example6.result")
  
  
  //7: unit is resolved against several nodes, but still lowered correctly:
  val proofg = ProofParserSPASS.read("examples/proofs/SPASS/example7.spass")
  println("FINALG: \n " + FOLowerUnits(proofg))
  val resultg = checkProofs(FOLowerUnits(proofg), "examples/proofs/SPASS/testresults/FOLowerUnits/example7.result")

  //8: unit can't be lowered
  val proofh = ProofParserSPASS.read("examples/proofs/SPASS/example8.spass")
  println("FINALH: \n " + FOLowerUnits(proofh))
  val resulth = checkProofs(FOLowerUnits(proofh), "examples/proofs/SPASS/testresults/FOLowerUnits/example8.result")

  //9: the unit is the relativley least general form 
  val proofi = ProofParserSPASS.read("examples/proofs/SPASS/example9.spass")
  println("FINALI: \n " + FOLowerUnits(proofi))
  val resulti = checkProofs(FOLowerUnits(proofi), "examples/proofs/SPASS/testresults/FOLowerUnits/example9.result")

  
  var usedVars = MSet[Var]()
  val x = new Var("X", i)
  val a = new Var("a", i)
  usedVars += x
  val y = new Var("Y", i)
  usedVars += y
  val u = new Var("U", i)
  usedVars += u
  val v = new Var("V", i)
  usedVars += v  

  //method level tests
  //apply
  //-- tested above; skipped

  //collectUnits
  //'Empty' proof
  val collect1result = FOLowerUnits.collectUnits(Proof(Axiom(Sequent()())))
  val collect1expected = (List[SequentProofNode](), MSet[Var]())

  //One unit, one var -- note nothing is lowered, since the unit is never resolved against anything, so the unit
  // is not returned
  val collect2result = FOLowerUnits.collectUnits(Proof(Axiom(Sequent(App(Var("q", i -> i), x))())))
  val collect2expected = (List[SequentProofNode](), MSet[Var](x))
  
  //one units, no vars -- note nothing is lowered, since the unit is never resolved against anything, so the unit
  // is not returned
  val collect3result = FOLowerUnits.collectUnits(Proof(Axiom(Sequent(App(Var("q", i -> i), a))())))
  val collect3expected = (List[SequentProofNode](), MSet[Var]())

  //fixProofNodes
  //empty
  val emptyAx = Axiom(Sequent()())
  val emptyProof = Proof[SequentProofNode](emptyAx)
  val fixProof1result = FOLowerUnits.fixProofNodes(Set[SequentProofNode](), emptyProof, MSet[Var]())
  val fixProof1expected = MMap[SequentProofNode, SequentProofNode]()
  fixProof1expected.update(emptyAx, emptyAx)

  //contractAndUnify
  //left is unit, right not
  val unitTest = Axiom(App(Var("q", i -> i), x) +: Sequent(App(Var("q", i -> i), a))())
  val unitTestB = Axiom(Sequent()(App(Var("q", i -> i), a)))
  val conUnif1result = FOLowerUnits.contractAndUnify(unitTestB, unitTest, usedVars, List[SequentProofNode]()) //TODO replace list with actual list of units
  
  //left is unit, right unit
  val unitTestC = Axiom(Sequent(App(Var("q", i -> i), a))())
  val conUnif2result = FOLowerUnits.contractAndUnify(unitTestB, unitTestC, usedVars, List[SequentProofNode]())//TODO replace list with actual list of units
  
  //left is not unit, right unit
  val nonUnitTest = Axiom(Sequent()(App(Var("p", i -> i), x)) + App(Var("p", i -> i), y))
  val unitTestD = Axiom(Sequent(App(Var("p", i -> i), a))())
  val conUnif3result = FOLowerUnits.contractAndUnify(nonUnitTest, unitTestD, usedVars,  List[SequentProofNode]())//TODO replace list with actual list of units
    
  //left is not unit, right is not unit 
  val nonUnitTestB = Axiom(Sequent()(App(Var("p", i -> i), x)) + App(Var("q", i -> i), y))  
  val unitTestE = Axiom(App(Var("p", i -> i), u) +: Sequent(App(Var("r", i -> i), v))())
  val conUnif4result = FOLowerUnits.contractAndUnify(nonUnitTestB, unitTestE, usedVars,  List[SequentProofNode]())//TODO replace list with actual list of units  
    
  
  //checkListUnif
  //empty list
  val checkListUnif1a = List[E]()
  val checkListUnif1result = FOLowerUnits.checkListUnif(checkListUnif1a, usedVars)
  val checkListUnif1expected = false

  //list is unifiable - single
  val checkListUnif2a = List[E](App(Var("q", i -> i), x))
  val checkListUnif2result = FOLowerUnits.checkListUnif(checkListUnif2a, usedVars)
  val checkListUnif2expected = true

  //list is not unifiable
  val checkListUnif3a = List[E](App(Var("q", i -> i), x)) ++ List[E](App(Var("r", i -> i), x))
  val checkListUnif3result = FOLowerUnits.checkListUnif(checkListUnif3a, usedVars)
  val checkListUnif3expected = false

  //list is unifiable - many
  val checkListUnif4a = List[E](App(Var("q", i -> i), x)) ++ List[E](App(Var("q", i -> i), y)) ++ List[E](App(Var("q", i -> i), u))
  val checkListUnif4result = FOLowerUnits.checkListUnif(checkListUnif4a, usedVars)
  val checkListUnif4expected = true


  //isUnitClause
  //empty
  val isUnit1 = Sequent()()

  //unit
  val isUnit2 = Sequent(App(Var("q", i -> i), x))()

  //non-unit
  val isUnit3 = Sequent(App(Var("q", i -> i), x))(App(Var("r", i -> i), y))
  
  println("---")
  println("Testing proof: \n " + FOLowerUnits(proofd))

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
    
    
    "determine if a clause is unit (empty)" in {
      FOLowerUnits.isUnitClause(isUnit1) must beEqualTo(false)
    }
    "determine if a clause is unit (unit)" in {
      FOLowerUnits.isUnitClause(isUnit2) must beEqualTo(true)

    }
    "determine if a clause is unit (non-unit)" in {
      FOLowerUnits.isUnitClause(isUnit3) must beEqualTo(false)
    }

    "check that list of formulas are unifiable (empty)" in {
      checkListUnif1result must beEqualTo(checkListUnif1expected)
    }
    "check that list of formulas are unifiable (single)" in {
      checkListUnif2result must beEqualTo(checkListUnif2expected)
    }
    "check that list of formulas are unifiable (non-unifiable)" in {
      checkListUnif3result must beEqualTo(checkListUnif3expected)
    }
    "check that list of formulas are unifiable (many)" in {
      checkListUnif4result must beEqualTo(checkListUnif4expected)
    }
    "collect units and unifiable variables correctly (no units, no vars)" in {
      collect1expected must beEqualTo(collect1result)
    }
    "collect units and unifiable variables correctly (one units, one var)" in {
      collect2expected must beEqualTo(collect2result)
    }
    "collect units and unifiable variables correctly (one units, no vars)" in {
      collect3expected must beEqualTo(collect3result)
    }    
    "contract and unify correctly (unit, unit)" in {
      conUnif1result.conclusion must beEqualTo(Sequent()())
    }
    "contract and unify correctly (unit, nonunit)" in {
      conUnif2result.conclusion must beEqualTo(Sequent()())
    }
    "contract and unify correctly (nonunit, unit)" in {
      conUnif3result.conclusion must beEqualTo(Sequent()())
    }
    "contract and unify correctly (nonunit, nonunit)" in {
      conUnif4result.conclusion must beEqualTo(Sequent(App(Var("r", i -> i), v))(App(Var("q", i -> i), y)))
    }    
    "fix proof nodes correctly (empty proof)" in {
      fixProof1result must beEqualTo(fixProof1expected)
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

    if (findRenaming(nodes.head.conclusion, seqs.head)(vars) != null) {
      return checkSequents(nodes.tail, seqs.tail)
    } else {
      println("desired not found " + nodes.head.conclusion + " AND " + seqs.head)
      false
    }
  }
}