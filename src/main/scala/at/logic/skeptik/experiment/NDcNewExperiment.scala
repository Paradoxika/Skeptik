package at.logic.skeptik.experiment

import scala.language.implicitConversions

import at.logic.skeptik.algorithm.generator.FormulaGenerator
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.natural.Assumption
import at.logic.skeptik.proof.natural.{ImpElim => ImpE}
import at.logic.skeptik.proof.natural.ImpElimC
import at.logic.skeptik.proof.natural.{ImpIntro => ImpI}
import at.logic.skeptik.proof.natural.ImpIntroCK
import at.logic.skeptik.judgment.{NaturalSequent,NamedE}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.prover.{SimpleProver, SimpleSaturationProver}
import collection.mutable.{Map => MMap}
import at.logic.skeptik.util.time._
import java.io.{File,PrintWriter}
import java.util.Calendar
import java.text.SimpleDateFormat
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.natural.{ImpElim => ImpE}
import at.logic.skeptik.proof.natural.{ImpIntro => ImpI}
import scala.collection.mutable.{Map => MMap, HashSet => MSet}

object NDcNewExperiment {

  def main(args: Array[String]): Unit = {
    
    val ndProver = new SimpleSaturationProver(Seq(ImpI),Seq(ImpE))
    
    println()
    println()
    
    
    def subsets[A](s: Set[A], maxSize: Int): Set[Set[A]] = {
      val sets = for (l <- 1 to maxSize) yield s.subsets(l).toSet 
      (sets.head /: sets.tail)((s1, s2) => s1 union s2)
    }
   
    var nameCounter = 0
    def getFreshName(): String = {
      nameCounter = nameCounter + 1
      "n" + nameCounter
    }
    
    def generateAxioms(nAtoms: Int, maxLength: Int, maxContextSize: Int, maxSameFormulaIntros: Int): Seq[Assumption] = {
      val formulas = (for (l <- 1 to maxLength) 
                     yield FormulaGenerator.generateAllRelaxed(l,nAtoms)).flatten
      
      val namedFormulas = (for (m <- 1 to maxSameFormulaIntros) yield formulas.map(NamedE(getFreshName(), _)) ).flatten
        
      val contexts = subsets(namedFormulas.toSet, maxContextSize)
           
      val axioms = (contexts flatMap {c => for (e <- c) yield new Assumption(c, e)}).toSeq.sortWith((a1,a2) => a1.conclusion.msize < a2.conclusion.msize)
      
      axioms
    }
    
    val axioms = generateAxioms(3,3,2,2)
    
    for (a <- axioms) println(a.conclusion + "          " + a.conclusion.msize +  "    " + a.conclusion.context.size  )
    println(axioms.size)
    
    ndProver.saturate(axioms, new NaturalSequent(Set(), Var("ImpossibleGoal", o)))
    
  }
}
