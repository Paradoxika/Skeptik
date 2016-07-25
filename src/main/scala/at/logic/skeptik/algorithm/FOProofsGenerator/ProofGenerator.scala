package at.logic.skeptik.algorithm.FOProofsGenerator

import at.logic.skeptik.expression.Var
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}

import collection.mutable.{Set => MSet}




/**
  * The class ProofGenerator implements methods to create
  * first order proofs.
  *
  * @param numberOfConstants  The top limit on the number of constants in the proofs generated
  * @param numberOfPredicates The top limit on the number of predicates in the proofs generated
  * @param numberOfVariables  The top limit on the number of variables in the proofs generated
  * @param numberOfFunctions  The top limit on the number of functions in the proofs generated
  */
class ProofGenerator(val proofHeight : Int, val numberOfConstants : Int = 5 , val numberOfPredicates : Int = 15,
                     val numberOfVariables : Int = 20, val numberOfFunctions :Int = 3) {


  private var variables : MSet[Var] = MSet[Var]()

  private def generateContraction(conclusion : Sequent) : Sequent = ???
  private def generateResolution(conclusion : Sequent) : (Sequent,Sequent) = ???
  private def generateResolutionSharingPremise(leftParent : Sequent, rightParent : Sequent) : (Sequent,Sequent) = ???


  def generateProof : Proof[Node] = generateProof(Sequent()())

  def generateProof(baseNode : Sequent) : Proof[Node] = {

    def convertNodeIntoProof(root : Node) : Proof[Node] = Proof(root)

    def generatePremises(sequent : Sequent) : Node = {
      def isEmptyClause(sequent : Sequent) : Boolean = sequent.ant.isEmpty && sequent.suc.isEmpty
      if(isEmptyClause(sequent)) {
        val (leftSequent,rightSequent) = generateResolution(sequent)
        val leftPremise  : Node        = generatePremises(leftSequent)
        val rightPremise : Node        = generatePremises(rightSequent)
        UnifyingResolution(leftPremise,rightPremise,sequent)(variables)
      } else {
        ???
        // TODO: Randomly choose between Resolution, Contraction and adding irregularitiess
      }
    }

    convertNodeIntoProof(generatePremises(baseNode))
  }
}
