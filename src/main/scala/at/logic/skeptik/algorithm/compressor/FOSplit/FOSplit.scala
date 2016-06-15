package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.{E, Var}
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.parser.TPTPParsers.ProofParserCNFTPTP
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}

import collection.mutable.{Set => MSet}

object FOSplitTest {
  def main(args: Array[String]): Unit = {
    val proof     = ProofParserCNFTPTP.read("examples/proofs/TPTP/splitTest2.tptp")
    val variables = ProofParserCNFTPTP.getVariables
    println("Original Proof:")
    print("Variables: ")
    println(variables.mkString(","))
    println("Proof:")
    println(proof)
    val split     = new TestSplt(variables,Atom("q",Nil))
    println("Proof splited over q")
    println(split(proof))
    val split2    = new TestSplt(variables,Atom("p",Nil))
    println("Proof splited over p")
    println(split2(proof))
  }
}

/**
  * The class FOSplit is the base of the split procedure in First-Order logic
  */
abstract class FOSplit(val variables : MSet[Var]) extends (Proof[Node] => Proof[Node]) {

  def equalLiterals(selectedLiteral : E , nodeLiteral : E) : Boolean

  def selectLiteral(proof: Proof[Node]): E

  def split(proof: Proof[Node], selectedLiteral : E): (Node,Node) = {
    def manageContraction(node : Node, fixedPremises : Seq[(Node,Node)]) : (Node , Node) = {
      require(fixedPremises.length == 1)
      val (left,right) = fixedPremises.head
      (Contraction.contractIfPossible(left,variables),Contraction.contractIfPossible(right,variables))
    }

    def manageResolution(node : Node ,fixedPremises : Seq[(Node,Node)]) : (Node,Node) = {
      def seqContains(sequent: Seq[E], literal: E): Boolean = {
        def equalNames(selectedLiteral: E, nodeLiteral: E): Boolean =
          (selectedLiteral, nodeLiteral) match {
            case (Atom(Var(name1, _), _), Atom(Var(name2, _), _)) => name1 == name2
            case (Atom(Var(name1, _), _), _) => false
            case _ => throw new Exception("The literal is not an instance of an Atom\nLiterals: " + selectedLiteral.toString + ", " + nodeLiteral.toString)
          }
        sequent.exists(equalNames(literal, _))
      }
      def containsPos(sequent: SeqSequent, literal: E) : Boolean = seqContains(sequent.suc,literal)
      def containsNeg(sequent: SeqSequent, literal: E) : Boolean = seqContains(sequent.ant,literal)
      def contains(sequent: SeqSequent, literal: E) : Boolean = containsPos(sequent,literal) || containsNeg(sequent,literal)

      require(fixedPremises.length == 2)
      lazy val (fixedLeftPos, fixedLeftNeg) = fixedPremises.head
      lazy val (fixedRightPos, fixedRightNeg) = fixedPremises.last
      val (leftPremise, rightPremise, leftResolvedLiteral, rightResolvedLiteral) =
        node match {
          case UnifyingResolution(lp, rp, lrl, rrl) => (lp, rp, lrl, rrl)
        }
      if (equalLiterals(selectedLiteral, leftResolvedLiteral)) {
        val premiseWithPositiveOcurrence =
          if(fixedLeftPos.conclusion.suc.exists(equalLiterals(leftResolvedLiteral,_)))
            fixedLeftPos
          else
            fixedRightPos
        val premiseWithNegativeOcurrence =
          if(fixedRightNeg.conclusion.ant.exists(equalLiterals(leftResolvedLiteral,_)))
            fixedRightNeg
          else
            fixedLeftNeg

          (premiseWithPositiveOcurrence,premiseWithNegativeOcurrence)
        //(fixedLeftPos, fixedRightNeg)
      } else {
        val (leftConclusionPos, leftConclusionNeg) = (fixedLeftPos.conclusion, fixedLeftNeg.conclusion)
        val (rightConclusionPos, rightConclusionNeg) = (fixedRightPos.conclusion, fixedRightNeg.conclusion)
        val finalLeftProof =
          if(!contains(leftConclusionPos,leftResolvedLiteral)) fixedLeftPos
          else if(!contains(rightConclusionPos,rightResolvedLiteral)) fixedRightPos
          else if(containsPos(leftConclusionPos,leftResolvedLiteral) && containsNeg(rightConclusionPos,rightResolvedLiteral)) UnifyingResolution.resolve(fixedLeftPos,fixedRightPos,variables)
          else if(containsNeg(leftConclusionPos,leftResolvedLiteral) && containsPos(rightConclusionPos,rightResolvedLiteral)) UnifyingResolution.resolve(fixedLeftPos,fixedRightPos,variables)
          else fixedRightPos // This is arbitrary
        val finalRighttProof =
          if(!contains(leftConclusionNeg,leftResolvedLiteral)) fixedLeftNeg
          else if(!contains(rightConclusionNeg,rightResolvedLiteral)) fixedRightNeg
          else if(containsPos(leftConclusionNeg,leftResolvedLiteral) && containsNeg(rightConclusionNeg,rightResolvedLiteral)) UnifyingResolution.resolve(fixedLeftNeg,fixedRightNeg,variables)
          else if(containsNeg(leftConclusionNeg,leftResolvedLiteral) && containsPos(rightConclusionNeg,rightResolvedLiteral)) UnifyingResolution.resolve(fixedLeftNeg,fixedRightNeg,variables)
          else fixedRightNeg // This is arbitrary
        (finalLeftProof,finalRighttProof)
      }

    }

    proof foldDown { (node: Node, fixedPremises: Seq[(Node, Node)]) =>
      node match {
        case Axiom(_)                    => (node, node)
        case Contraction(_,_)            => manageContraction(node, fixedPremises)
        case UnifyingResolution(_,_,_,_) => manageResolution(node, fixedPremises)
      }
    }

  }


  def applyOnce(p: Proof[Node]): Proof[Node] = {
    val selectedLiteral = selectLiteral(p)
    val (left, right)   = split(p, selectedLiteral)
    val leftContracted  = Contraction.contractIfPossible(left,variables)
    val rightContracted = Contraction.contractIfPossible(right,variables)
    val compressedProof : Proof[Node] = UnifyingResolution.resolve(leftContracted,rightContracted,variables)
    if (compressedProof.size < p.size) compressedProof else p
  }
}

abstract class SimpleSplit(override val variables : MSet[Var], val literal : E) extends FOSplit(variables) {
  def selectLiteral(proof: Proof[Node]) : E = literal
  def apply(p: Proof[Node]):Proof[Node] = applyOnce(p)
}

class TestSplt(override val variables : MSet[Var], override val literal : E)
extends SimpleSplit(variables,literal) with NameEquality