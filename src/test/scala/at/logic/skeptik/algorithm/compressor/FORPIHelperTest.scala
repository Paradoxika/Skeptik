package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.expression._
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.parser.ParserException
import scala.io.Source
import at.logic.skeptik.parser.SequentParser
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.Contraction
import java.io.PrintWriter
import java.io.File
import at.logic.skeptik.judgment.immutable.{ SetSequent => IClause }


import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner


@RunWith(classOf[JUnitRunner])
class FORPILUHelperSpecification extends SpecificationWithJUnit   {

      var usedVars = MSet[Var]()
  val x = new Var("X", i)
  val a = new Var("a", i)
  val b = new Var("b", i)
      val c = new Var("c", i)
      
  usedVars += x
  val y = new Var("Y", i)
  usedVars += y
 
  val z = new Var("Z", i)
  usedVars += z  
  
    val u = new Var("U", i)
  usedVars += u  
  
    val v = new Var("V", i)
  usedVars += v  
  
    val w = new Var("W", i)
  usedVars += w  


  
  
  //July 18 tests
    val follows = App(App(Var("follows", i -> (i -> i)), u), v)
    val succeeds = App(App(Var("succeeds", i -> (i -> i)), w), u)
    val succeedsB = App(App(Var("succeeds", i -> (i -> i)), w), v)
//(follows p8 p3), (succeeds p3 p3), (labels loop p3), (succeeds p3 p8))
      val p8 = new Var("p8", i)
            val loop = new Var("loop", i)

      val p3 = new Var("p3", i)
          val labels = App(App(Var("labels", i -> (i -> i)), loop), p3)

      val followsC = App(App(Var("follows", i -> (i -> i)), p8), p3)
    val succeedsC = App(App(Var("succeeds", i -> (i -> i)), p3), p3)
    val succeedsCB = App(App(Var("succeeds", i -> (i -> i)), p3), p3)
    
    val found = Sequent()(follows) + succeeds + succeedsB
    val actual = Sequent()(followsC) + succeedsC + succeedsCB + labels
    
    val resultNew = FORPIHelperTester.finalCheckTest(found, actual)
    println(resultNew)
    
    
     //⊢ (succeeds W U), (succeeds U V), (succeeds W V)
        val BsucceedsA = App(App(Var("succeeds", i -> (i -> i)), w), u)
            val BsucceedsB = App(App(Var("succeeds", i -> (i -> i)), u), v)
                val BsucceedsC = App(App(Var("succeeds", i -> (i -> i)), w), v)
                
        val BActsucceedsA = App(App(Var("succeeds", i -> (i -> i)), p3), p3)
            val BActsucceedsB = App(App(Var("succeeds", i -> (i -> i)), p3), p8)
                val BActsucceedsC = App(App(Var("succeeds", i -> (i -> i)), u), v) 
                
    val Bfound = Sequent()(BsucceedsA) + BsucceedsB + BsucceedsC
    val Bactual = Sequent()(BActsucceedsA) + BActsucceedsB + BActsucceedsC 
    
    val BresultNew = FORPIHelperTester.finalCheckTest( Bactual, Bfound)
    println(BresultNew)  
    
    
    // (a_member_of W U), (a_member_of V U), (path_connected U), (a_path_from_to_in (skf3 U V W) W V U)
    val amember =   App(App(Var("a_member_of", i -> (i -> i)), w), u)
    val amemberB =   App(App(Var("a_member_of", i -> (i -> i)), v), u)
    val path =   App(Var("path_connected", i -> i), u)
    val apath =   App(App(App(App(Var("a_path_from_to_in", i -> (i-> (i-> (i->i))) ), AppRec(new Var("skf3", i -> (i -> (i -> i))), List(u,v,w))), w), v), u)
    
    //(a_member_of skc5 skc3), (path_connected skc3), (a_path_from_to_in (skf3 skc3 skc4 skc5) skc5 skc4 skc3), (a_member_of skc4 skc3)
          val skc5 = new Var("skc5", i)
          val skc4 = new Var("skc4", i)      
      val skc3 = new Var("skc3", i)
    val Actamember =   App(App(Var("a_member_of", i -> (i -> i)), skc5), skc3)
    val ActamemberB =   App(App(Var("a_member_of", i -> (i -> i)), skc4), skc3)
    val Actpath =   App(Var("path_connected", i -> i), skc3)
    val Actapath =   App(App(App(App(Var("a_path_from_to_in", i -> (i-> (i-> (i->i))) ), AppRec(new Var("skf3", i -> (i -> (i -> i))), List(skc3,skc4,skc5))), skc5), skc4), skc3)
        
    
    val Cfound = Sequent()(amember) + amemberB + path + apath
    val Cactual = Sequent()(Actamember) + ActamemberB + Actpath + Actapath
    
    val CresultNew = FORPIHelperTester.finalCheckTest(Cfound, Cactual)
    println(CresultNew)    
    
    
    //(a_path_from_to_in U V W X), (a_group_isomorphism_from_to (alpha_hat U) (first_homotop_grp X V) (first_homotop_grp X W))
    val Dapath = App(App(App(App(Var("a_path_from_to_in", i -> (i-> (i-> (i->i))) ), u), v), w), x)
    val ahat = AppRec(new Var("alpha_hat", i -> i), List(u))
    val firstHom = AppRec(new Var("first_homotop_grp", i -> (i-> i)), List(x,v))
    val firstHomB =  AppRec(new Var("first_homotop_grp", i -> (i-> i)), List(x,w))
    val DgroupIso = App(App(App(Var("a_group_isomorphism_from_to", i -> (i->(i->(i->i)))), ahat), firstHom), firstHomB) 
    
    //(a_member_of skc5 skc3), 
    //(a_group_isomorphism_from_to (alpha_hat NEW0) (first_homotop_grp skc3 skc5) (first_homotop_grp skc3 skc4)),
    //(a_path_from_to_in (skf3 skc3 skc4 skc5) skc5 skc4 skc3))
    val Dactmem =   App(App(Var("a_member_of", i -> (i -> i)), skc5), skc3)
    val Dactskf = AppRec(new Var("skf3", i -> (i -> (i -> i))), List(skc3,skc4,skc5))
    val Dactapath = App(App(App(App(Var("a_path_from_to_in", i -> (i-> (i-> (i->i))) ), Dactskf), skc5), skc4), skc3)
    val N0 = new Var("NEW0", i)
    usedVars += N0
      val actahat = AppRec(new Var("alpha_hat", i -> i), List(N0))
    val actfirstHom = AppRec(new Var("first_homotop_grp", i -> (i-> i)), List(skc3,skc5))
    val actfirstHomB =  AppRec(new Var("first_homotop_grp", i -> (i-> i)), List(skc3,skc4))
    val DactDgroupIso = App(App(App(Var("a_group_isomorphism_from_to", i -> (i->(i->(i->i)))), actahat), actfirstHom), actfirstHomB)     

    val Dfound = Sequent()(Dapath) + DgroupIso
    val Dactual = Sequent()(Dactmem) + DactDgroupIso + Dactapath
    println(Dfound)
    println(Dactual)
    val DresultNew = FORPIHelperTester.finalCheckTest(Dfound, Dactual)
    println(DresultNew) 
   
  
  "FORPILUHelpers" should {
    "finalCheck must check containment" in {
      resultNew must beEqualTo(true)
    }
    "finalCheck must check containment (many possible unification targets)" in {
      BresultNew must beEqualTo(true)
    }
    "finalCheck must check containment - second test" in {
      CresultNew must beEqualTo(true)
    }
    "finalCheck must not always return true" in {
      DresultNew must beEqualTo(false)
    }
  }
}
object FORPIHelperTester extends FOAbstractRPIAlgorithm  with FOCollectEdgesUsingSafeLiterals with checkProofEquality {
   def apply(proof: Proof[SequentProofNode]) = {
proof //STUB
  }  
	protected def computeSafeLiterals(proof: SequentProofNode,
			childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
			edgesToDelete: FOEdgesToDelete): IClause = {
	  //STUB
			childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof) } match {
			case Nil =>
			if (!childrensSafeLiterals.isEmpty) edgesToDelete.markBothEdges(proof)
			proof.conclusion.toSetSequent
			case h :: t =>
			t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) =>
			{
				acc intersect safeLiteralsFromChild(v, proof, edgesToDelete)
			}
			}
			}
	}

  def finalCheckTest(safeLit: Sequent, seqToDelete: Sequent) = {
    finalCheck(safeLit,seqToDelete)
  }
}