package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import collection.mutable.{ HashSet => MSet }

import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{Axiom}
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.resolution.FindsVars
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

/*
 * jgorzny
 * Nov 2016
 * 
 * Note: not all inference rules are supported.
 * 
 */

object ProofParserSkeptikOutput extends ProofCombinatorParser[Node] with SkeptikOutputParsers with SkeptikSequentParser

trait SkeptikOutputParsers
extends JavaTokenParsers with RegexParsers with  SkeptikSequentParser with FindsVars {
  
  private var proofMap = new MMap[Int,Node]
  private var exprMap = new MMap[Int,E]
  private var vars = MSet[Var]()

  def reset() = {
    proofMap = new MMap[Int,Node]
    exprMap = new MMap[Int,E]
  }
  
  def proof: Parser[Proof[Node]] = rep1(pline) ^^ { list => 
    Proof(list.last)
  }
    

  
  def proofLine: Parser[(Int, (Sequent, (String, List[Int])))] =  """.""".r ^^ { 
    SkeptikSequentParser(_)
  } 
  
  def pline: Parser[Node] = line ^^ {
    case pair => {
      val lineNum = pair._1
      val seq = pair._2._1
      val nodeInfo = pair._2._2
      val nodeType = nodeInfo._1
      val nodeRefs = nodeInfo._2
      
      val out = if (nodeType.equals("Axiom")){
        Axiom(seq)
      } else if (nodeType.equals("Contraction")){
        val premise = proofMap.get(nodeRefs.head).get
        val newVars = getSetOfVars(premise)
        vars = vars ++ newVars
        Contraction(premise, seq)(vars) //TODO: add the new vars?
      } else {
        //UR
        val left = proofMap.get(nodeRefs(0)).get
        val right = proofMap.get(nodeRefs(1)).get
        val newVarsL = getSetOfVars(left)
        val newVarsR = getSetOfVars(right)
        vars = vars ++ newVarsL ++ newVarsR
        UnifyingResolution(left, right, seq)(vars) //TODO: add the new vars?        
      }
      
      proofMap += (lineNum -> out)
      
      out
    }
  }




}
