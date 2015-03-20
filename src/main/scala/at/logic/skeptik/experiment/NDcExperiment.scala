package at.logic.skeptik.experiment

import scala.language.implicitConversions

import at.logic.skeptik.algorithm.generator.FormulaGenerator
import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula.{Imp, enrichFormula, depth}
import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.measure
import at.logic.skeptik.proof.natural.Assumption
import at.logic.skeptik.proof.natural.ImpElim
import at.logic.skeptik.proof.natural.ImpElimC
import at.logic.skeptik.proof.natural.ImpIntro
import at.logic.skeptik.proof.natural.ImpIntroC
import at.logic.skeptik.judgment.NaturalSequent
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.prover.SimpleProver
import collection.mutable.{Map => MMap}
import at.logic.skeptik.util.time._
import java.io.{File,PrintWriter}
import java.util.Calendar
import java.text.SimpleDateFormat
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{Map => MMap, HashSet => MSet}

object NDcExperiment {

  def main(args: Array[String]): Unit = {
    
    val ndProver = new SimpleProver(Seq(Assumption,ImpIntro,ImpElim))
    val ndcProver = new SimpleProver(Seq(Assumption,ImpIntroC,ImpElimC))

    implicit def formulaToNaturalSequent(f: E) = new NaturalSequent(Set(), f)

    //val b = "B"^o
    //val c = "C"^o
    //val f = (((c → c) → ((c → c) → b)) → b)
    //println(f)
    //val p = ndProver.prove(f,maxheight=9)
    //val p2 = ndcProver.prove(f,maxheight=5)
    //println(p)
    //println(p2)
    //return
    
    val maxtime = 30000 //milliseconds

    val alreadyGenerated = new MSet[E]
    
    var goals = 0
    var proved = 0
    var failed = 0
    var compressed = 0
    
    def factorial(n:Long) = ((1 to n.toInt) :\ 1) ( _ * _ )
    def catalan(n:Long) = ((((n+1).toInt to (2*n).toInt) :\ 1) ( _ * _ )) / factorial(n+1)
    
    def maxGoals(l: Int) = {
      if (l > 10) 1000
      else if (l == 10) 1000
      else if (l > 2) catalan(l-1)/2
      else 0
    }
    
    val l = args(0).toInt // formula length
    val s = args(1).toInt // number of distinct symbols
    
    val now = new SimpleDateFormat("yyyyMMdd-HHmmss").format(Calendar.getInstance().getTime())
    val file = new File("experiments/NDc/report-" + l + "-" + s + "-" + now + ".txt" )
    val fp = new PrintWriter(file)
    
    for (length <- l to l; numSymbols <- s to s) {
    //for (length <- 3 to 20; numSymbols <- 1 to (length-1)) {
      alreadyGenerated.dropWhile { x => true } // freeing memory
      
      for (i <- 1 to maxGoals(length)) {
        if (i % 100 == 0) fp.flush()
        print(length + " " + numSymbols + " " + i + " : ")
  
        var g = FormulaGenerator.generateOne(length,numSymbols)
        while (alreadyGenerated contains g) g = FormulaGenerator.generateOne(length,numSymbols)
        alreadyGenerated += g
        
        goals += 1
       
        val d = depth(g)
        print(d + " " + g + " : ")
        
        
        val Timed(ndP,ndT) = timed { ndProver.prove(g, timeout = maxtime, maxheight = 20) }
        
        ndP match {
          case Some(ndProof) => {
            proved += 1
            
            val ndM = measure(ndProof)
  
            print("length/height: " + ndM("length") + " " + ndM("height") + " ; ")
            
            val Timed(ndcP,ndcT) = timed { ndcProver.prove(g, timeout = 10 * maxtime, maxheight = ndM("height")) }
            ndcP match {
              case Some(ndcProof) => {
                val ndcM = measure(ndcProof)
  
                print("length/height: " + ndcM("length") + " " + ndcM("height"))
                
                if (ndcM("length") < ndM("length")) {
                  compressed += 1
                }
                print(" ; totals: " + goals + " " + proved + " " + failed + " " + compressed)
                print(" \n")
                fp.println(List(length,numSymbols,d,g,ndT,ndM("length"),ndM("height"),ndM("coreSize"),ndcT,ndcM("length"),ndcM("height"),ndcM("coreSize")).mkString(","))
              }
              case None => {
                fp.println(List(length,numSymbols,d,g,ndT,ndM("length"),ndM("height"),ndM("coreSize"),ndcT,-1,-1,-1).mkString(","))
                failed += 1
                print("None \n") 
              }
            }
          }
          case None => {
            fp.println(List(length,numSymbols,d,g,ndT,-1,-1,-1,-1,-1,-1,-1).mkString(","))
            print("None \n") 
          }
        }
      }

    }
    
    fp.close()
  }
}
