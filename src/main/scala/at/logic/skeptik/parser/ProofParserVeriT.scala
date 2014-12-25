package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap, HashSet => MSet}
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference,EqCongruent,EqTransitive,EqReflexive,EqSymmetry}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.ArrayBuffer

object ProofParserVeriT extends ProofCombinatorParser[Node] with VeriTParsers

trait VeriTParsers
extends JavaTokenParsers with RegexParsers {
  
//  private var proofMap = new MMap[Int,Node]
  private val proofArray = new ArrayBuffer[Node]()
  private var exprMap = new MMap[Int,E]
  private var bindMap = new MMap[String,E]

  def proof: Parser[Proof[Node]] = rep(line) ^^ { list => 
    val p = Proof(list.last)
//    proofMap = new MMap[Int,Node]
    proofArray.clear
    exprMap = new MMap[Int,E]
    p
  }
  def line: Parser[Node] = "(set"  ~> proofName ~ "(" ~ inference <~ "))" ^^ {
    case ~(~(n, _), p) => {
//      proofMap += (n -> p); p
      proofArray += p
      p
    }
    case wl => throw new Exception("Wrong line " + wl)
  }
  
  def equality: Parser[Node] = (eq_congruent | eq_reflexive | eq_transitive)
  
  def eq_congruent: Parser[Node] = "eq_congruent" ~> conclusion ^^ {
    list => EqCongruent(list)
  }
  
  def eq_reflexive: Parser[Node] = "eq_reflexive" ~> conclusion ^^ {
    list => EqReflexive(list)
  }
  
  def eq_transitive: Parser[Node] = "eq_transitive" ~> conclusion ^^ {
    list => EqTransitive(list)
  }
  
  def inference: Parser[Node] = (resolution | axiom | equality |unchecked)
  def resolution: Parser[Node] = "resolution" ~> premises <~ conclusion ^^ {
//    list => resolveClauses(list)
    list => {
      (list.head /: list.tail) { (left, right) => 
        try { 
          R(left, right)
        }
        catch {
        	case e: Exception => {
        	  
        	  throw(e)
        	}
        }
      }
    }
  }
  
    /**
   * Resolves the clauses represented by a list of indices in the correct order.
   * 
   * It does this by keeping track of in which clauses variables occur positively/negatively.
   * This method only initializes these maps and calls the recursive method res with them.
   */
  def resolveClauses(clauses: List[Node]): Node = {
    //map denoting that variable v occurs in {clause_1,...,clause_n} as a positive literl
    val posOc = MMap[E,MSet[Node]]()
    //respective negative version
    val negOc = MMap[E,MSet[Node]]()
    //initialize the maps
    clauses.foreach(clause => {
      clause.conclusion.suc.foreach(v => {
//        println(v + " occurs positively in " + clause)
        if (posOc.isDefinedAt(v)) posOc(v) += clause
        else posOc += (v -> MSet[Node](clause))
      })
      clause.conclusion.ant.foreach(v => {
        if (negOc.isDefinedAt(v)) negOc(v) += clause
        else negOc += (v -> MSet[Node](clause))
      })
    })
    //start recursion
    res(posOc,negOc)
  }
  
  /**
   * Recursively resolves clauses, given two maps for positive/negative occurances of variables
   * 
   * For TraceCheck chains, the following invariant holds:
   * At every point either 
   * there exists a literal which occurs exactly once positively and once negatively
   * or there is only one clause remaining
   * 
   * In the first case, this literal is used for resolving the respective clauses and updating the
   * occurange maps
   * In the other case, the one clause is returned 
   * (either when no pivot is found or when the resolved clause is empty)
   */
  def res(posOc: MMap[E,MSet[Node]], negOc: MMap[E,MSet[Node]]):Node = {
    val nextPivot = posOc.find(e => {
      e._2.size == 1 &&
      negOc.getOrElse(e._1, MSet[Node]()).size == 1
    }).map(a => a._1)
    nextPivot match {
      //no more pivot means posOc and/or negOc can only contain 1 clause in the sets of occurances
      case None => 
        if (posOc.size > 0) posOc.last._2.last 
        else negOc.last._2.last
      case Some(p) => {
        val posClause = posOc(p).last
        val negClause = negOc(p).last
        val newClause = R(posClause,negClause,p,false)
        newClause.conclusion.suc.foreach(v => {
          posOc.get(v) match {
            case None => posOc += (v -> MSet[Node](newClause))
            case Some(set) => {
              set -= posClause
              set -= negClause
              set += newClause
            }
          }
        })
        newClause.conclusion.ant.foreach(v => {
          negOc.get(v) match {
            case None => negOc += (v -> MSet[Node](newClause))
            case Some(set) => {
              set -= posClause
              set -= negClause
              set += newClause
            }
          }
        })
        if (posOc.contains(p) || negOc.contains(p)) {
          val newPOc = posOc - p
          val newNegOc = negOc - p
          if (newPOc.isEmpty && newNegOc.isEmpty) newClause
          else res(newPOc,newNegOc)
        }
        else newClause
      }
    }
  }

  
  def axiom: Parser[Node] = "input" ~> conclusion ^^ {
    list => new Axiom(list)
  }
  def unchecked: Parser[Node] = name ~ opt(premises) ~ opt(args) ~ conclusion ^^ {
    case ~(~(~(name, None),_), list) => new UncheckedInference(name,Seq(),list)
    case ~(~(~(name, Some(premises)),_), list) => new UncheckedInference(name,premises,list)
  }

  def premises: Parser[List[Node]] = ":clauses (" ~> rep(proofName) <~ ")" ^^ {
    list => list map {pn => proofArray(pn - 1)}
//    list => list map proofMap
  }

  def args: Parser[List[Int]] = ":iargs (" ~> rep("""\d+""".r) <~ ")" ^^ {
    list => list map { _.toInt }
  }
  def conclusion: Parser[List[E]] = ":conclusion (" ~> rep(expression) <~ ")"


  def proofName: Parser[Int] = ".c" ~> """\d+""".r ^^ { _.toInt }
  
  def expression: Parser[E] = (assignment | namedExpr | expr)
  
  def assignment: Parser[E] = exprName ~ ":" ~ expr ^^ {
    case ~(~(n,_),e) => {
      exprMap += (n -> e); e
    }
  }

  def exprName: Parser[Int] = "#" ~> """\d+""".r ^^ { _.toInt }
  
  def namedExpr: Parser[E] = exprName ^^ { exprMap(_) }
  
  def expr: Parser[E] = (variable | app | let)

  def let: Parser[E] = "(" ~> "let" ~> "(" ~> rep(binding) ~> ")" ~> expression <~ ")" ^^ { e =>
    bindMap = new MMap[String,E]
    e
  }

  def binding: Parser[Any] = "(" ~> name ~ expression <~ ")" ^^ {
    case ~(sym, exp) => bindMap += (sym -> exp) ; ()
  }

  // ToDo: this parser is not distinguishing formulas and terms.
  // Terms are (wrongly) given type o.
  // As long as theory inferences are parsed as UncheckedInferences,
  // this will not be a problem.
  
  def variable: Parser[E] = name ^^ { v => bindMap.getOrElse(v, Var(v,o)) }
 
  private val predefinedBigSymbols = Map(
    "and" -> bigAndC ,
    "or" -> bigOrC 
  )
    
  private val predefinedSymbols = Map(
    "imp" -> impC ,
    "not" -> negC ,
    "=" -> eqC(o)
  ) 
  
 private val equalitySymbols = Map(
    "not" -> negC ,
    "=" -> eqC(o)
  ) 
  
  def app: Parser[E] = "(" ~> name ~ rep(expression) <~ ")" ^^ {
    case ~(functionSymbol, args) => {
      val function = predefinedBigSymbols.get(functionSymbol) match {
        case None => predefinedSymbols.get(functionSymbol) match {
          case None => Var(functionSymbol, (args :\ (o: T)) {(a, t) => (o -> t)})
          case Some(c) => c
        }
        case Some(c) => c(args.length)
      } 
      ((function: E) /: args)((e,a) => App(e,a))
    }
  } 
  
  def name: Parser[String] = """[^ ():]+""".r
}
