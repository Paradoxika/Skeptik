package at.logic.skeptik.experiment.proving

import at.logic.skeptik.algorithm.generator.FormulaGenerator
import at.logic.skeptik.expression.E
import at.logic.skeptik.expression.formula.Imp
import at.logic.skeptik.expression.o
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.natural.Assumption
import at.logic.skeptik.proof.natural.{ImpElim => ImpE}
import at.logic.skeptik.proof.natural.ImpElimC
import at.logic.skeptik.proof.natural.{ImpIntro => ImpI}
import at.logic.skeptik.proof.natural.{ImpIntroC,ImpIntroCK}
import at.logic.skeptik.judgment.{Judgment, Sequent, NamedE, NaturalSequent}
import at.logic.skeptik.prover.SimpleProver
import collection.mutable.{Map => MMap}
import at.logic.skeptik.util.time._
import language.implicitConversions

import java.io.{File,PrintWriter}

import java.util.Calendar
import java.text.SimpleDateFormat

object ProverExperiment {

  def run(args: Array[String]): Unit = {
    
    val ndProver = new SimpleProver(Seq(Assumption,ImpI,ImpE))
    //val ndcProver = new SimpleProver2(Seq(Assumption,ImpIntroC,ImpElimC))
    val ndcProver = new SimpleProver(Seq(Assumption,ImpI,ImpElimC))
    val ndckProver = new SimpleProver(Seq(Assumption,ImpIntroCK,ImpElimC))
    
    val provers = Seq(//("ND", ndProver), 
                      ("NDc", ndcProver)//, 
                      //("NDck", ndckProver)
                      )
    
    println()
    
//    val goals = FormulaGenerator.generateAll(3,2)
//    val i = 22; val j = 4
//    val goals = Seq(FormulaGenerator.generateOne(i,j),
//        FormulaGenerator.generateOne(i,j),
//        FormulaGenerator.generateOne(i,j),
//        FormulaGenerator.generateOne(i,j))
        
    val goals = Seq(
                    //FormulaGenerator.generateExample(0),
                    //FormulaGenerator.generateExample(1),
                    FormulaGenerator.generateExample(2)//,
                    //FormulaGenerator.generateExample(3)
                    )

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
        val maxtime = 60000 //milliseconds
        val result = timed(repetitions) { p._2.prove(g, timeout = maxtime) }
        
        val resultTimeMS = (result.time * 1000).toInt // microseconds
        println("Prover " + p._1 + ": " +
                (if (result.result != None) "proved in " + resultTimeMS + " microseconds"
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
