package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.algorithm.compressor.FOSplit.equalities.NameEquality
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
    val proof     = ProofParserCNFTPTP.read("/home/eze/Escritorio/TPTP-Parsers/tests/splitTest.tptp")
    val variables = ProofParserCNFTPTP.getSeenVars
    println(variables)
    println(proof)
    val split     = new TestSplt(variables,Atom("p",Nil))
    split(proof)
    println(proof)
  }
}
/**
  * The class FOSplit
  */
abstract class FOSplit(val variables : MSet[Var]) extends (Proof[Node] => Proof[Node]) {

  def equalLiterals(selectedLiteral : E , nodeLiteral : E) : Boolean

  def selectLiteral(proof: Proof[Node]): E

  def split(proof: Proof[Node], selectedLiteral : E): (Node,Node) = {
    def manageContraction(node : Node, fixedPremises : Seq[(Node,Node)]) : (Node , Node) = {
      require(fixedPremises.length == 1)
      val (left,right) = fixedPremises.head
      (Contraction(left)(variables),Contraction(right)(variables))
    }

    def manageResolution(node : Node ,fixedPremises : Seq[(Node,Node)]) : (Node,Node) = {
      def contains(sequent : SeqSequent,literal : E) : Boolean = {
        sequent.ant.filter(equalLiterals(literal,_)).nonEmpty || sequent.suc.filter(equalLiterals(literal,_)).nonEmpty
      }
      require(fixedPremises.length == 2)
      lazy val (fixedLeftPos, fixedLeftNeg)   = fixedPremises.head
      lazy val (fixedRightPos, fixedRightNeg) = fixedPremises.last
      val (leftPremise,rightPremise,leftResolvedLiteral,rightResolvedLiteral) =
        node match {
          case UnifyingResolution(lp, rp, lrl, rrl) => (lp, rp, lrl, rrl)
        }
      if(equalLiterals(selectedLiteral,leftResolvedLiteral)) (fixedLeftPos, fixedRightNeg)
      else {
        val (leftConclusionPos, leftConclusionNeg) = (fixedLeftPos.conclusion, fixedLeftNeg.conclusion)
        val (rightConclusionPos, rightConclusionNeg) = (fixedRightPos.conclusion, fixedRightNeg.conclusion)
        val finalLeftProof =
          if(!contains(leftConclusionPos,leftResolvedLiteral)) fixedRightPos
          else if(!contains(rightConclusionPos,rightResolvedLiteral)) fixedLeftPos
          else UnifyingResolution.resolve(fixedLeftPos,fixedRightPos,variables)
        val finalRighttProof =
          if(!contains(leftConclusionNeg,leftResolvedLiteral)) fixedRightNeg
          else if(!contains(rightConclusionNeg,rightResolvedLiteral)) fixedLeftNeg
          else UnifyingResolution.resolve(fixedLeftNeg,fixedRightNeg,variables)
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
    val leftContracted  = Contraction(left)(variables)
    val rightContracted = Contraction(right)(variables)
    val compressedProof : Proof[Node] = UnifyingResolution.resolve(leftContracted,rightContracted,variables)
    println(compressedProof)
    compressedProof//if (compressedProof.size < p.size) compressedProof else p
  }
}

abstract class SimpleSplit(override val variables : MSet[Var], val literal : E) extends FOSplit(variables) {
  def selectLiteral(proof: Proof[Node]) : E = literal
  def apply(p: Proof[Node]):Proof[Node] = applyOnce(p)
}

class TestSplt(override val variables : MSet[Var], override val literal : E)
extends SimpleSplit(variables,literal) with NameEquality