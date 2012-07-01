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

object ProverExperiment {

  def main(args: Array[String]): Unit = {
    
    val ndProver = new SimpleProver2(Seq(Assumption,ImpI,ImpE))
    val ndcProver = new SimpleProver2(Seq(Assumption,ImpIntroC,ImpElimC))
    val ndckProver = new SimpleProver2(Seq(Assumption,ImpIntroCK,ImpElimC))
    
    val provers = Seq(("ND", ndProver), 
                      ("NDc", ndcProver), 
                      ("NDck", ndckProver))
    
    println()
    
    val goals = (new FormulaGenerator).generate(3,3)
//    val goals = Seq(Imp(
//                        Imp(
//                            Imp(Prop("A"),Prop("B")),
//                            Prop("B")
//                            ),
//                        Prop("A")
//                        )
//                   )
    println(goals.length)

    implicit def formulaToNaturalSequent(f: E) = new NaturalSequent(Set(), f)
    implicit def formulaToSequent(f: E) = Sequent(Nil, f)
    
    val results = MMap[(E, String),Timed[Option[Proof[_,_]]]]()
    for (g <- goals) {
      println("Goal: " + g)
      for (p <- provers) {
        val repetitions = 3
        val maxtime = 1000 * repetitions
        results((g, p._1)) = timeout(maxtime) { timed(repetitions) { p._2.prove(g) } } match {
          case Some(timedResult) => timedResult
          case None => Timed(None, 10 * maxtime)
        }
        val r0 = "Prover " + p._1 + ": " 
        val r1 = if (results((g, p._1)).result != None) "proved in " + results((g, p._1)).time + "microseconds"
                 else if (results((g, p._1)).time > maxtime*1000) "timed out"
                 else "found no proof in " + results((g, p._1)).time + "microseconds" 
        println(r0 + r1)
      }
    }
  }
}
