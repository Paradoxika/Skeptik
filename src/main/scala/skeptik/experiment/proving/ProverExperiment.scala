package skeptik.experiment.proving

import skeptik.algorithm.generator.FormulaGenerator
import skeptik.expression.E
import skeptik.expression.formula.{Prop,Imp}
import skeptik.expression.o
import skeptik.proof.Proof
import skeptik.proof.ProofNodeCollection
import skeptik.proof.natural.Assumption
import skeptik.proof.natural.{ImpElim => ImpE}
import skeptik.proof.natural.ImpElimC
import skeptik.proof.natural.{ImpIntro => ImpI}
import skeptik.proof.natural.{ImpIntroC,ImpIntroCK}
import skeptik.judgment.{Judgment, Sequent, NamedE, NaturalSequent}
import skeptik.prover.SimpleProver2
import collection.mutable.{Map => MMap}
import skeptik.util.time._

import java.io.{File,PrintWriter}

import java.util.Calendar
import java.text.SimpleDateFormat

object ProverExperiment {

  def run(args: Array[String]): Unit = {
    
    val ndProver = new SimpleProver2(Seq(Assumption,ImpI,ImpE))
    val ndcProver = new SimpleProver2(Seq(Assumption,ImpIntroC,ImpElimC))
    val ndckProver = new SimpleProver2(Seq(Assumption,ImpIntroCK,ImpElimC))
    
    val provers = Seq(("ND", ndProver), 
                      ("NDc", ndcProver), 
                      ("NDck", ndckProver))
    
    println()
    
//    val goals = FormulaGenerator.generateAll(3,2)
//    val i = 22; val j = 4
//    val goals = Seq(FormulaGenerator.generateOne(i,j),
//        FormulaGenerator.generateOne(i,j),
//        FormulaGenerator.generateOne(i,j),
//        FormulaGenerator.generateOne(i,j))
        
    val goals = Seq(FormulaGenerator.generateExample(0),
                    FormulaGenerator.generateExample(1),
                    FormulaGenerator.generateExample(2),
                    FormulaGenerator.generateExample(3))

    println(goals.length)
    
    val now = new SimpleDateFormat("yyyyMMdd-HHmmss").format(Calendar.getInstance().getTime())
    val file = new File("experiments/NDc/report-" + now + ".txt" )
    val fp = new PrintWriter(file)
    
    implicit def formulaToNaturalSequent(f: E) = new NaturalSequent(Set(), f)
    implicit def formulaToSequent(f: E) = Sequent(Nil, f)
    
    val results = MMap[(E, String),Timed[Option[Proof[_,_]]]]()
    for (g <- goals) {
      println("Goal: " + g)
      fp.print(g)
      for (p <- provers) {
        val repetitions = 1
        val maxtime = 1000 * repetitions //milliseconds
        val result = timeout(maxtime) { timed(repetitions) { p._2.prove(g) } } match {
          case Some(timedResult) => timedResult
          case None => Timed(None, 10 * maxtime)
        }
        
        val resultTimeMS = (result.time * 1000).toInt // microseconds
        println("Prover " + p._1 + ": " +
                (if (result.result != None) "proved in " + resultTimeMS + " microseconds"
                 else if (result.time > maxtime) "timed out"
                 else "found no proof in " + resultTimeMS + " microseconds" ))
        fp.print(", " + resultTimeMS)
        fp.print(", " + (result.result match {
          case None => -1
          case Some(p) => ProofNodeCollection(p).size
        }))
        results((g, p._1)) = result
      }
      fp.println
    }
    
    fp.close()
  }
}
