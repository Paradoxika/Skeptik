package at.logic.skeptik.experiment

import scala.language.implicitConversions

import at.logic.skeptik.algorithm.generator.FormulaGenerator
import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula.{Imp, enrichFormula}
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

    val provers = Seq(("ND", ndProver), ("NDc", ndcProver))

    println()

    
    val now = new SimpleDateFormat("yyyyMMdd-HHmmss").format(Calendar.getInstance().getTime())
    val file = new File("experiments/NDc/report-" + now + ".txt" )
    val fp = new PrintWriter(file)

    implicit def formulaToNaturalSequent(f: E) = new NaturalSequent(Set(), f)

    val maxtime = 30000 //milliseconds

    val alreadyGenerated = new MSet[E]
    
    var goals = 0
    var proved = 0
    var failed = 0
    var compressed = 0
    
    def factorial(n:Long) = ((1 to n.toInt) :\ 1) ( _ * _ )
    def catalan(n:Long) = ((((n+1).toInt to (2*n).toInt) :\ 1) ( _ * _ )) / factorial(n+1)
    
    
    def maxGoals(l: Int) = {
      if (l > 10) 10000
      else if (l == 10) 1000
      else if (l > 2) catalan(l-1)/2
      else 0
    }
    
    val a = "A"^o
    val b = "B"^o
    
    //val f = ((a → a) → a) → a
    
    //val f = (((a → b) → a) → (b → a))
    
//    val ndP = ndProver.prove(f, maxtime, 4)
//    ndP match { 
//      case Some(ndProof) => {
//        println(ndProof)
//        println(measure(ndProof)); 
//      } 
//      case None => println("None") 
//    }
//    println()
    
//    val ndcP = ndcProver.prove(f, maxtime, 4)
//    ndcP match { 
//      case Some(ndcProof) => println(measure(ndcProof)); 
//      case None => println("None") 
//    }
    
    for (length <- 3 to 20; numSymbols <- 1 to (length-1)) {
      alreadyGenerated.dropWhile { x => true } // freeing memory
      
      for (i <- 1 to maxGoals(length)) {
        if (i % 100 == 0) fp.flush()
        print(length + " " + numSymbols + " " + i + " : ")
  
        var g = FormulaGenerator.generateOne(length,numSymbols)
        while (alreadyGenerated contains g) g = FormulaGenerator.generateOne(length,numSymbols)
        alreadyGenerated += g
        
        goals += 1
        
        //val g = FormulaGenerator.generateExample(i + 1)
  
        print(g + " : ")
        
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
                fp.println(List(g,ndT,ndM("length"),ndM("height"),ndM("coreSize"),ndcT,ndcM("length"),ndcM("height"),ndcM("coreSize")).mkString(","))
              }
              case None => {
                fp.println(List(g,ndT,ndM("length"),ndM("height"),ndM("coreSize"),ndcT,-1,-1,-1).mkString(","))
                failed += 1
                print("None \n") 
              }
            }
          }
          case None => {
            fp.println(List(g,ndT,-1,-1,-1,-1,-1,-1,-1).mkString(","))
            print("None \n") 
          }
        }
      }

    }

    println()
    println(goals + " " + proved + " " + compressed)
    
//    val results = MMap[(E, String),Timed[Option[ProofNode[_,_]]]]()
//    for (g <- goals) {
//      println("Goal: " + g)
//      fp.print(g)
//      for (p <- provers) {
//        val repetitions = 1
//
//        val result = timed(repetitions) { p._2.prove(g, timeout = maxtime) }
//
//        val resultTimeMS = (result.time * 1000).toInt // microseconds
//        println("Prover " + p._1 + ": " +
//                (if (result.result != None) "proved in " + resultTimeMS + " microseconds"
//                 else "found no proof in " + resultTimeMS + " microseconds" ))
//        fp.print(", " + resultTimeMS)
//        fp.print(", " + (result.result match {
//          case None => -1
//          case Some(p) => Proof(p).size
//        }))
//        results((g, p._1)) = result
//      }
//      fp.println
//    }

    fp.close()
  }
}
