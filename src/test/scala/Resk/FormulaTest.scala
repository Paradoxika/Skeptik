package Resk

import ResK.expressions._
import ResK.judgments._
import ResK.proofs._
import ResK.formulas._
import ResK.positions._
import ResK.formulaAlgorithms._
import ResK.proofs.naturalDeductionWithSequentNotation.{ ImpElim, ImpIntro, Axiom => NDAxiom }
import ResK.proofs.naturalDeduction.{ NamedE, ImpElim => ImpE, ImpIntro => ImpI, Assumption }
import ResK.proofs.naturalDeduction.{ ImpElimC, ImpIntroC }

import ResK.provers.SimpleProver
import ResK.provers.SimpleProverWithSideEffects

import ResK.proofs.ProofNodeCollection

import ResK.formulaGenerator._

import scala.collection.immutable.{ HashSet => ISet }
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class FormulaTest extends SpecificationWithJUnit {

  "Formula generator" should {
    "produce 47 items for (2,4)" in {
      val goals = generate2(2, 4)
      goals must have length 47
    }
    "produce 58 items for (2,5)" in {
      val goals = generate2(2, 5)
      goals must have length 58
    }
  }
}
