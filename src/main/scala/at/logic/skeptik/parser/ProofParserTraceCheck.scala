package at.logic.skeptik.parser

import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import scala.util.parsing.combinator._
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import collection.mutable.{HashMap => MMap, HashSet => MSet}
import collection.immutable.{HashMap => Map, HashSet => Set}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._

/**
 * The grammar for traces is:
 *    
 * <trace>       = { <clause> }
 * <clause>      = <pos> <literals> <antecedents>
 * <literals>    = "*" | { <lit> } "0"
 * <antecedents> = { <pos> } "0"
 * <lit>         = <pos> | <neg>
 * <pos>         =  "1" |  "2" | .... | <max-idx>
 * <neg>         = "-"<pos>
 * 
 * 
 */

object ProofParserTraceCheck extends ProofCombinatorParser[Node] with TraceCheckParsers

trait TraceCheckParsers
extends BasicTraceCheckParsers {
  
  private var proofMap = new MMap[Int,Node]
  private var clauseNumbers = new MMap[Int,(List[E],List[Int])]
  var nodeMap = MMap[Sequent,Node]()
  var processedMap = MMap[List[Int],Node]();
  var maxClause = 0

  def reset() = {
    proofMap = new MMap[Int,Node]
    varMap = new MMap[Int,E]
    clauseNumbers = new MMap[Int,(List[E],List[Int])]
    nodeMap = MMap[Sequent,Node]()
    processedMap = MMap[List[Int],Node]();
    maxClause = 0
  }
  
  
  def proof: Parser[Proof[Node]] = rep(clause) ^^ { list => 
    Proof(getNode(list.last))
  }
  
  def clause: Parser[Int] = pos ~ literals ~ antecedents ^^ {
    case ~(~(p, l), a) => {
        if (l.isEmpty && a.isEmpty) throw new Exception("Invalid input at " + p + " ~ " + l)
        else {
          clauseNumbers += (p -> (l,a))
          if (maxClause < p) {
            maxClause = p
          }
          maxClause
        }
      }
    case wl => throw new Exception("Wrong line " + wl)
  }
  
  /**
   * Resolves the clauses represented by a list of indices in the correct order.
   * 
   * It does this by keeping track of in which clauses variables occur positively/negatively.
   * This method only initializes these maps and calls the recursive method res with them.
   */
  def resolveClauses(clauseNumbers: List[Int]): Node = {
    //map denoting that variable v occurs in {clause_1,...,clause_n} as a positive literl
    val posOc = MMap[E,MSet[Node]]()
    //respective negative version
    val negOc = MMap[E,MSet[Node]]()
    //initialize the maps
    clauseNumbers.foreach(cln => {
      val clause = getNode(cln)
      clause.conclusion.suc.foreach(v => {
//        println(v + " occurs positively in " + clause)
        if (posOc.isDefinedAt(v)) posOc(v) += clause
        else posOc += (v -> MSet[Node](clause))
      })
      clause.conclusion.ant.foreach(v => {
//        println(v + " occurs negatively in " + clause)
        if (negOc.isDefinedAt(v)) negOc(v) += clause
        else negOc += (v -> MSet[Node](clause))
      })
    })
    //start recursion
    res(posOc,negOc)
  }
  
  /**
   * Recursively resolves clauses, given two maps for 
   * positive/negative occurrences of variables
   * 
   * For TraceCheck chains, the following invariant holds:
   * At every point either 
   * there exists a literal which occurs exactly once positively and once negatively
   * or there is only one clause remaining
   * 
   * In the first case, this literal is used for resolving the respective clauses and updating the
   * occurrence maps
   * In the other case, the one clause is returned 
   * (either when no pivot is found or when the resolved clause is empty)
   */
  def res(posOc: MMap[E,MSet[Node]], negOc: MMap[E,MSet[Node]]):Node = {
    val nextPivot = posOc.find(e => {
      e._2.size == 1 &&
      negOc.getOrElse(e._1, MSet[Node]()).size == 1
    }).map(a => a._1)
//    println(nextPivot)
    nextPivot match {
      //no more pivot means posOc and/or negOc can only contain 1 clause in the sets of occurrences
      case None => 
        if (posOc.size > 0) posOc.last._2.last 
        else negOc.last._2.last
      case Some(p) => {
        val posClause = posOc(p).last
        val negClause = negOc(p).last
        val resolvent = R(posClause,negClause,p,false)
        val newClause = nodeMap.getOrElseUpdate(resolvent.conclusion, resolvent)
        newClause.conclusion.suc.foreach(v => {
          posOc(v) -= posClause
          posOc(v) -= negClause
          posOc(v) += newClause
        })
        newClause.conclusion.ant.foreach(v => {
          negOc(v) -= posClause
          negOc(v) -= negClause
          negOc(v) += newClause
        })
        val newPOc = posOc - p
        val newNegOc = negOc - p
        if (newPOc.isEmpty && newNegOc.isEmpty) newClause
        else res(newPOc,newNegOc)
      }
    }
  }
    
  def getNode(index: Int): Node = {
    val tuple = clauseNumbers(index)
    if (tuple._2.isEmpty) {
      val ax = new Axiom(tuple._1)
      val con = ax.conclusion
      nodeMap.getOrElseUpdate(con, ax)
    }
    else {
      processedMap.getOrElseUpdate(tuple._2,resolveClauses(tuple._2))
    }
  }
}
  
trait BasicTraceCheckParsers
extends JavaTokenParsers with RegexParsers {
 
  var varMap = new MMap[Int,E]
  
  def pos: Parser[Int] = """[1-9][0-9]*""".r ^^ { _.toInt }
  
  def neg: Parser[Int] = """-[1-9][0-9]*""".r ^^ { _.toInt }
  
  def literals: Parser[List[E]] = (ommittedLits | (lits <~ "0"))
  
  def ommittedLits: Parser[List[E]] = "*" ^^ { case _ => List[E]() } 
  
  def lits: Parser[List[E]] = rep(lit)
  
  def lit: Parser[E] = (pos | neg) ^^ {l => 
    if (l > 0) varMap.getOrElseUpdate(l,new Var(l.toString,o))
    else varMap.getOrElseUpdate(l,new App(negC,new Var(l.abs.toString,o)))
  }
  
  def antecedents: Parser[List[Int]] = rep(pos) <~ "0"
}