package skeptik.experiment.proving

import skeptik.algorithm.generator.FormulaGenerator
import skeptik.expression.Var
import skeptik.expression.formula.{Prop,Imp}
import skeptik.expression.o
import skeptik.proof.ProofNodeCollection
import skeptik.proof.natural.Assumption
import skeptik.proof.natural.{ImpElim => ImpE}
import skeptik.proof.natural.ImpElimC
import skeptik.proof.natural.{ImpIntro => ImpI}
import skeptik.proof.natural.ImpIntroC
import skeptik.proof.natural.NamedE
import skeptik.prover.SimpleProverWithSideEffects

object ProverExperiment {

  def main(args: Array[String]): Unit = {
   
    val ndProver = new SimpleProverWithSideEffects(Seq(ImpE,ImpI,Assumption))
    val ndcProver = new SimpleProverWithSideEffects(Seq(Assumption,ImpIntroC,ImpElimC))

    
    val context = Set[NamedE]()
    
    println()
    
    val goals = (new FormulaGenerator).generate(7,7)
    println(goals.length)

    
    println()
    
    var yesCounter = 0
    var noCounter = 0
    var yesCCounter = 0
    var noCCounter = 0
    var cumulativeSize = 0
    var size = 0
    var cumulativeCSize = 0
    var cSize = 0
    for (goal <- goals) {
      //println(goal)
      System.gc()
      val proof = ndProver.prove(goal,context)
      println("goal" + goal + " ; " + proof)
      val provable = proof match {
        case None => {noCounter += 1; "no"} 
        case Some(p) => {yesCounter += 1;
                         size = ProofNodeCollection(p).size
                         cumulativeSize += size
                         "yes"}
      }
      println("started proving " + goal)
      val deepProof =  ndcProver.prove(goal,context)
      println("finished proving " + goal + " ; " + deepProof)
      val deepProvable = deepProof match {
        case None => {noCCounter += 1; "no"} 
        case Some(p) => {
            yesCCounter += 1; 
            cSize = ProofNodeCollection(p).size
            if (proof != None) cumulativeCSize += cSize
            "yes"}
      }
      //println("ho")
      if (true) println(yesCounter + " , " + noCounter + " , " + provable + " , " + size + " , " + cumulativeSize + " , " + deepProvable + " , " + cSize + " , " + cumulativeCSize + "  , goal:" + goal)
    }
    
    println("yes: " + yesCounter)
    println("no:" + noCounter)
    println("yesC: " + yesCCounter)
    println("noC:" + noCCounter)
    println("cumulativeSize: " + cumulativeSize)
    println("cumulativeCSize: " + cumulativeCSize)
    
  }

}
