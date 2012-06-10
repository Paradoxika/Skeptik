package skeptik

import skeptik.expressions._
import skeptik.judgments._
import skeptik.proofs._
import skeptik.formulas._
import skeptik.positions._
import skeptik.formulaAlgorithms._
import skeptik.proofs.naturalDeductionWithSequentNotation.{ ImpElim, ImpIntro, Axiom => NDAxiom }
import skeptik.proofs.naturalDeduction.{ NamedE, ImpElim => ImpE, ImpIntro => ImpI, Assumption }
import skeptik.proofs.naturalDeduction.{ ImpElimC, ImpIntroC }

import skeptik.provers.SimpleProver
import skeptik.provers.SimpleProverWithSideEffects

import skeptik.proofs.ProofNodeCollection

import skeptik.formulaGenerator._

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
