package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

object ProofParserLFSC extends ProofParser[Node] with LFSCParsers

trait LFSCParsers
extends JavaTokenParsers with RegexParsers {
  
  private var proofMap = new MMap[String,Node]
  private var exprMap = new MMap[String,E]
  private var varMap = new MMap[String,E]
  
  //returns the actual proof
 def proof: Parser[Proof[Node]] = "(check " ~ rep(varDecl) ~ ")" ^^ {   
 	case ~(~(_,list),_)=>{ //ignore everything but the clauses (which will include the resolutions)
 		val p = Proof((list.last).last)
 		exprMap = new MMap[String,E]
 		p
    }
  }
  

  def varDecl: Parser[List[Node]] = "($ " ~ name ~ clauseOrVar ~ ")" ^^{
    case ~(~(~(_,_),m),_) => {
      m
    }
  } 
  
  def clauseOrVar: Parser[List[Node]] = (varDecl | rep(clause))
  
  
  //parse either a clause, or a resolution
  def clause : Parser[Node] = (clausel | resolves)
 
    //parse a clause -- should now work with any number of literals
  def clausel : Parser[Node] = "($ " ~ cname ~ "(holds " ~ literalSeq ~ ")" ^^{
    case ~(~(~(~(_,n),_),l),_) =>{
      val ax = new Axiom(l)
      proofMap += (n -> ax)
      ax
    }
  } 
  
  def literalSeq : Parser[List[E]] = (emptyLit | lit)
  
  def emptyLit : Parser[List[E]] = "cln" ^^{
    s=>List()
  }
  
  def lit : Parser[List[E]] = "(clc (" ~ literal ~ ")"  ~ literalSeq ~ ")" ^^{
    case ~(~(~(~(_,e),_),l),_) => {
      List(e) ::: l
    }
  }
  
  def literal : Parser[E] = (pn ~ vname) ^^{
  case ~(true, v) => exprMap.getOrElseUpdate(v.toString+"_pos",new Var(v.toString,o))
  case ~(false, v) => exprMap.getOrElseUpdate(v.toString+"_neg",new App(negC,new Var(v.toString,o)))
}
    
  def resolves: Parser[Node] = "(R _ _ _ " ~ nameOrResSubTree ~ nameOrResSubTree ~ cname ~")" ^^ {
    case ~(~(~(~(_,f),s),_),_) => {
      R(f,s)
    } 
  }
  
  def nameOrResSubTree: Parser[Node] = (axiom | resolves) 
  
  def axiom: Parser[Node] =  cname ^^ {
    f =>    proofMap.getOrElse(f, throw new Exception("Clause not defined yet"))
  }
  

  

  def pn: Parser[Boolean] = ("pos " | "neg ") ^^{
  	case "pos " => true
  	case "neg " => false
  }
  
  def cname: Parser[String] = """[^ ():]+""".r

  def vname: Parser[E] = """[^ ():]+""".r ^^{
    case s => 
      //add the variable to the bind list, just in case future work needs it
      varMap.getOrElseUpdate(s,new Var(s.toString,o))
  }

  
   def name: Parser[E] = str ~ "var"  ^^ {
    case ~(s,_) => {
      varMap.getOrElseUpdate(s,new Var(s.toString,o))
      
    }
  }

    def str: Parser[String] = """[^ ():]+""".r
    
    
}
