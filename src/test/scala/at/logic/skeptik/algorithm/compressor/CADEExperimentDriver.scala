package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.parser.ParserException
import scala.io.Source
import at.logic.skeptik.parser.SequentParser
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.expression._
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.Contraction
import java.io.PrintWriter

object CADEExperimentDriver extends checkProofEquality {

  def getProblems(file: String, path: String): MSet[String] = {
    val outTj = MSet[String]()

    for (line <- Source.fromFile(file).getLines()) {
      val newProblemN = path + "GoodProofs\\" + line.substring(0, 3) + "\\" + line + ".spass"
      println(newProblemN)
      outTj.add(newProblemN)
    }
    outTj
  }

  def main(args: Array[String]): Unit = {
    //    val path = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\"
    //    val proofList = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\good_all.txt"

    val path = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\"
    val proofList = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\all_good_nov10.txt"
//    val problemSetS = new MSet[String]()//getProblems(proofList, path)
          val problemSetS = getProblems(proofList, path)
//val problemSetS = getProblems(proofList, path).filter(_ == "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\GRP\\GRP028-1.spass")
//    problemSetS.add("C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\GRP\\GRP028-1.spass")
//problemSetS.add("C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SET\\SET833-2.spass")
    var errorCountT = 0
    var totalCountT = 0
    var noresT = 0
    var otherT = 0
    var mrrresT = 0
    var cantfindT = 0
    var reqfailT = 0
    var parseT = 0
    var mrrassumptionT = 0

//    val elogger = new PrintWriter("errors.elog")
//    val eTypeLogger = new PrintWriter("errorTypes.elog")
//    val eProblemsLogger = new PrintWriter("errorProblems.elog")
    val etempT = new PrintWriter("etemp.elog")

    for (probY <- problemSetS) {
//      val probX = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\GRP\\GRP028-1.spass"
      println(totalCountT + " " + probY)
//      etempT.println(probY + " " + totalCountT + " OVERFLOW")
//      etempT.flush
      totalCountT = totalCountT + 1
      var proofLengthII = 0
      try {

        val proofToTest = ProofParserSPASS.read(probY)

//        println("length: " + proof.size)
//        println(proof)
        proofLengthII = proofToTest.size
      etempT.println(probY + " " + proofLengthII + " ")
      etempT.flush        
        println(FOLowerUnits(proofToTest))
        //        FORecyclePivotsWithIntersection(proof)
      } catch {
        case pe: ParserException => {
          parseT = parseT + 1
          errorCountT = errorCountT + 1
          etempT.println(probY)
          etempT.flush()
        }
        case exce: Exception => {
//          eProblemsLogger.println(probY)
          if (exce.getMessage() != null) {
            if (exce.getMessage().equals("Resolution: the conclusions of the given premises are not resolvable. A")) {
              noresT = noresT + 1
              //              etemp.println(p)
              //              etemp.flush()
            } else if (exce.getMessage().equals("Resolution (MRR): the conclusions of the given premises are not resolvable.")) {
              mrrresT = mrrresT + 1
              etempT.println(probY + " " + proofLengthII + " MRR")
              etempT.flush()
            } else if (exce.getMessage().equals("Resolution: Cannot find desired resolvent")) {
              etempT.println(probY + " " + proofLengthII + " can't find")
              etempT.flush()
              cantfindT = cantfindT + 1
              //                            etemp.println(p)
              //              etemp.flush() 
            } else if (exce.getMessage().equals("MRR assumption failed")) {
              mrrassumptionT = mrrassumptionT + 1
            } else if (exce.getMessage().equals("requirement failed")) {
              reqfailT = reqfailT + 1
            } else {
              etempT.println(probY + " " + proofLengthII+ " other" + exce.getMessage())
              etempT.flush()
              otherT = otherT + 1
            }
          } else {
            otherT = otherT + 1
            etempT.println(probY + " " + proofLengthII + " other")
            etempT.flush()
          }
          errorCountT = errorCountT + 1
          exce.printStackTrace()
//          exce.printStackTrace(elogger)
//          elogger.flush
        }
      }
    }
    println("total: " + totalCountT)
    println("errors: " + errorCountT)
    println("   nores: " + noresT)
    println("   other: " + otherT)
    println("  mrrres: " + mrrresT)
    println("cantfind: " + cantfindT)
    println(" reqfail: " + reqfailT)
    println("   parse: " + parseT)
    println("mrrassumption: " + mrrassumptionT)

//    elogger.flush
//    eTypeLogger.flush
//    eProblemsLogger.flush
    //    ProofParserSPASS.read("C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\GoodProofs\\SYN\\SYN656-1.spass");

    //    ProofParserSPASS.read("C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\GoodProofs\\SWV\\SWV300-2.spass")

    //  val proofa = ProofParserSPASS.read("examples/proofs/SPASS/example1.spass")
    //  val computeda = FOLowerUnits(proofa).toString
    //  val expecteda = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example1.result").mkString
    //println(checkProofs(FOLowerUnits(proofa), "examples/proofs/SPASS/testresults/FOLowerUnits/example1.result"))

    // // val proof1 = ProofParserSPASS.read("examples/proofs/SPASS/completespaceforn_5.spass")
    //    val input = scala.io.Source.fromFile("examples/proofs/SPASS/testresults/FOLowerUnits/example1.result")
    //    val lines = input.getLines
    //    //val x = SequentParser(" x ")
    ////    SequentParser.proof(new scala.util.parsing.input.Reader("A"))
    //    //println("final: " + x)
    //    for(l <- lines){
    //       val x = SequentParser(l)
    //       println(x)
    //      //println(l)
    //    }
    ////  val proofb = ProofParserSPASS.read("examples/proofs/SPASS/example2.spass")
    ////  println(proofb)
    ////  val computedb = FOLowerUnits(proofb).toString
    ////  println(computedb)

    //      var usedVars = MSet[Var]()
    //  val x = new Var("X", i)
    //  val y = new Var("Y", i)
    //  val u = new Var("U", i)
    //val v = new Var("V", i)      
    //  val n = new Var("NEW2", i)
    //  val e = new Var("eq", i -> (i -> i))
    //  val f = new Var("f", i -> i)
    //  val two = new Var("2", i)
    //  val three = new Var("3", i)
    //  usedVars += x
    //  usedVars += y
    //    usedVars += u
    //  usedVars += v

    //  //First test case
    //  //(eq (f X) 2), (eq (f NEW2) 2) ⊢
    //  val f1A = AppRec(e, List(App(f, x), two))
    //  val f2A = AppRec(e, List(App(f, n), two))
    //
    //  val seqF2A = Sequent(f2A)()
    //  val seqA = f1A +: seqF2A
    //
    //  val premiseA = new Axiom(seqA)
    //
    //  val conA = Contraction(premiseA)(usedVars)
    //
    // 
    //
    //  val A = new Var("a", i -> i)
    //  val B = new Var("b", i -> i)
    //  val b = new Var("b", i)
    //  val a = new Var("a", i)
    //
    //
    //
    //  //mergeMaps
    //  //one empty, one full
    //  val emptyMap = MMap[Var, Set[E]]()
    //  val nonemptyMap = MMap[Var, Set[E]]((x, Set[E](App(A, x))))
    //  val mixedInput = Seq[MMap[Var, Set[E]]](emptyMap) ++ Seq[MMap[Var, Set[E]]](nonemptyMap)
    //  val mixedExpected = nonemptyMap
    //  val mixedInputOut = conA.mergeMaps(mixedInput)
    //  val unitTest = Axiom(Sequent(App(Var("q", i -> i), x))())
    //  val unitTestB = Axiom(Sequent()(App(Var("q", i -> i), x)))
    //  val conUnif1result = FOLowerUnits.contractAndUnify(unitTestB, unitTest, usedVars)

    //  val nonUnitTest = Axiom(Sequent()(App(Var("p", i -> i), x)) + App(Var("p", i -> i), y))
    //
    //    
    //  //left is not unit, right is not unit
    //  val unitTestE = Axiom(App(Var("p", i -> i), u) +: Sequent(App(Var("p", i -> i), v))())
    //  val conUnif4result = FOLowerUnits.contractAndUnify(nonUnitTest, unitTestE, usedVars)      

    //        class FindDesiredTest extends FindDesiredSequent {
    //  }
    //
    //  val tester = new FindDesiredTest
    //  
    //    
    //      var usedVars = MSet[Var]()
    //  val x = new Var("X", i)
    //  val a = new Var("a", i)
    //        val y = new Var("Y", i)
    //  usedVars += x
    //          val z = new Var("Z", i)
    //  usedVars += z
    //  usedVars += y
    //    
    //  val FDSpairsC = Seq[(E, E)]((App(Var("p", i -> i), x), App(Var("p", i -> i), z))) ++   Seq[(E, E)]((App(Var("q", i -> i), a), App(Var("q", i -> i), y)))
    //  println(FDSpairsC)
    //  val FDSdesiredC = Sequent(App(Var("p", i -> i), y))(App(Var("p", i -> i), x))
    //  val FDSleftC = Axiom(Sequent()(App(Var("p", i -> i), x)) + App(Var("q", i -> i), a))
    //  val FDSrightC = Axiom(App(Var("q", i -> i), y) +: Sequent(App(Var("p", i -> i), z))())
    //  val FDSleftCleanC = FDSleftC
    //  println("left: " + FDSleftC)
    //  println("right: " + FDSrightC)
    //  println("desired: " + FDSdesiredC)
    //  val FDSresultC = tester.findDesiredSequent(FDSpairsC, FDSdesiredC, FDSleftC, FDSrightC, FDSleftCleanC, false)(usedVars)
    //  //val FDSexpectedC = UnifyingResolution(FDSleftC, FDSrightC)(usedVars)  
    //
    //
    //  //println(tester.findDesiredSequent(FDSpairsC, FDSdesiredC, FDSleftC, FDSrightC, FDSleftCleanC, false)(usedVars))
    //    
  }
}



