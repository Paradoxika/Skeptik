package at.logic.skeptik.exporter

import at.logic.skeptik.expression.{E,Var,Abs,App,AppRec}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import java.io.Writer


abstract class Exporter(w: Writer) {
  def write(s: String) = w.write(s)
}

trait SequentExporterVeriT extends ExpressionExporterVeriT {
  def export(s: Sequent): Unit = {
    val disjuncts = (s.ant.map(f => neg(f)).view ++ s.suc)
    write("(")
    if (!disjuncts.isEmpty) {
      export(disjuncts.head)
      for (f <- disjuncts.tail) { 
        write(" ")
        export(f)       
      }
    } 
    write(")")
  }
}

trait ExpressionExporterVeriT extends Exporter {
  def export(e: E): Unit = e match {
    case Var(n,_) => {
      if (n == andS) write("and")
      else if (n == orS) write("or")
      else if (n == negS) write("not")
      else if (n == allS) write("all")
      else if (n == exS) write("all")
      else write(n)
    }
    case App(App(Var(p,_), e1), e2) if p == eqS => {
      write("(= ")
      export(e1)
      write(" ")
      export(e2)
      write(")")
    }
    case AppRec(f,args) => {
      write("(")
      export(f)
      for (a <- args) {
        write(" ")
        export(a)
      }
      write(")")
    }
    case _ => write(e.toString)
  }
}

class ProofExporterVeriT(w: Writer) extends Exporter(w) with SequentExporterVeriT {
  def export(proof:Proof[Node]): Unit = {
    var counter = 0
    
    proof foldDown { 
      (n, premiseResults: Seq[String]) => {
        val infName = n match {
          case Axiom(_) => "input"
          case R(_,_,_,_) => "resolution"
          case UncheckedInference(x,_,_) => x
        }
//        def beginInference() = {
//          
//        }
        
        def endInference() = {
          write(" :conclusion ")
          export(n.conclusion) 
          write ("))\n")
        }    
        n match {
          case Axiom(conclusion) => {
              val name = ".c" + counter
              counter += 1
              write("(set " + name + " (" + infName)
              endInference()
              name
          }
          case R(left,right,_,_) => {
            if (proof.childrenOf(n).length == 1) {
              "(" + premiseResults(0) + " " + premiseResults(1) + ")"
            }
            else {
              val name = ".c" + counter
              counter += 1
              val subproof = "(" + premiseResults(0) + " " + premiseResults(1) + ")"
              write("(set " + name + " (" + infName)
              write(" :clauses " + subproof) 
              endInference()
              name
            }
          }
          case UncheckedInference(_, premises, conclusion) => {
            val name = ".c" + counter
            counter += 1
            write("(set " + name + " (" + infName)
            if (!premiseResults.isEmpty) write(" :clauses " + premiseResults.mkString("("," ",")"))
            endInference()
            name
          }
        }  
      } 
    }
 
    w.close()
  }
}
