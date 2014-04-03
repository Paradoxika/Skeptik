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
  def proof: Parser[Proof[Node]] = "(check " ~ rep(varDecl) ~ rep(clause) ~ rep(paren) ^^ { 
    case ~(~(_,list),_)=>{ //ignore everything but the clauses (which will include the resolutions)
    val p = Proof(list.last)
    exprMap = new MMap[String,E]
    p
    }
  }
  
  def varDecl: Parser[String] = "($ " ~ name  ^^{
    case ~(_,c) => { 
    "" //return nothing -- we don't care about the variables (assumes input is well formed)
    }
  }
  
  def paren: Parser[String] = ")" //for those extra ones caused by variable declarations
       
  //parse either a clause, or a resolution
  def clause : Parser[Node] = (clausel | resolves)
    
  //parse a clause -- currently limited to clauses with only two variables, should generalize
    def clausel : Parser[Node] = "($ " ~ cname ~ "(holds (clc (" ~ pn ~ vname ~ ") (clc (" ~ pn ~ vname ~ ") cln)))" ^^{
      case ~(~(~(~(~(~(~(~(_,n),_),"neg "),fir),_),"pos "),sec),_) => {
        //not(v1) or (v2)
        //make the clause: add the variables, after getting them from the map if necessary
        //negate only the first one
      val ax = new Axiom(List(exprMap.getOrElseUpdate(fir.toString+"_neg",new App(negC,new Var(fir.toString,o))), exprMap.getOrElseUpdate(sec.toString+"_pos",new Var(sec.toString,o))))
      proofMap += (n -> ax)
      ax
      
     
    }
      case ~(~(~(~(~(~(~(~(_,n),_),"pos "),fir),_),"pos "),sec),_) => {
         //(v1) or (v2)
      val ax = new Axiom(List(exprMap.getOrElseUpdate(fir.toString+"_pos",new Var(fir.toString,o)), exprMap.getOrElseUpdate(sec.toString+"_pos",new Var(sec.toString,o))))
      proofMap += (n -> ax)
      ax
     
    }
      case ~(~(~(~(~(~(~(~(_,n),_),"neg "),fir),_),"neg "),sec),_) => {
         //not(v1) or not(v2)
      val ax = new Axiom(List(exprMap.getOrElseUpdate(fir.toString+"_neg",new App(negC,new Var(fir.toString,o))), exprMap.getOrElseUpdate(sec.toString+"_neg",new App(negC,new Var(sec.toString,o)))))
      proofMap += (n -> ax)
      ax
     
    }
      case ~(~(~(~(~(~(~(~(_,n),_),"pos "),fir),_),"neg "),sec),_) => { 
        //(v1) or not(v2)
      val ax = new Axiom(List(exprMap.getOrElseUpdate(fir.toString+"_pos",new Var(fir.toString,o)), exprMap.getOrElseUpdate(sec.toString+"_neg",new App(negC,new Var(sec.toString,o)))))
      proofMap += (n -> ax)
      ax
     
    }   

  }
  
  //parse a resolution
  def resolves: Parser[Node] = "(R _ _ _ " ~ nameOrRes ~ nameOrRes ~ cname ~")" ^^ {
    case ~(~(~(~(_,first),second),_),_) => {      
      //don't care about cname as we don't tell skeptik which variable to resolve on
      
      //find the appropriate clauses to resolve on, and then resolve on them
      R(proofMap.getOrElse(first, throw new Exception("Clause not defined yet")), 
          proofMap.getOrElse(second, throw new Exception("Clause not defined yet")))
    }
  }
    
  def nameOrRes: Parser[String] = (cname | resolves) ^^{
    case s:String => {
      //if it was the name of a clause, just return that name
      s
    }
    case n:Node => {
      //if it was a R(R(_,_),_) situation, the inner R(_,_) lacks a name; 
      // assign it one and return that name
      proofMap += (n.toString -> n)
      n.toString
    }
  }
  
  def pn: Parser[String] = ("pos " | "neg ")
  
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
