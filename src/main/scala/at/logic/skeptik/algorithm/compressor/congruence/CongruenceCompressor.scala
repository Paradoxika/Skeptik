package at.logic.skeptik.algorithm.compressor.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable._
import at.logic.skeptik.proof._
import at.logic.skeptik.congruence._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.algorithm.compressor._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}
import at.logic.skeptik.proof.Proof.apply
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.congruence.Congruence
import at.logic.skeptik.congruence.structure.EquationPath

/**
 * Object CongruenceCompressor is the actual proof compressing object
 * 
 * it gathers axioms from the whole proof and checks input derived nodes for redundant explanation
 * input derived nodes all are recursive children of the single input node in the proof file
 * to find redundant explanations for a node global axioms are used and 
 * axioms that where resolved with some recursive premise of the node are used
 * 
 * first the node is fixed, just like subsumption or other compression algorithms do
 * then for redundant fixed nodes new subproofs are generated from the EquationTree corresponding to the new explanation
 */
abstract class CongruenceCompressor extends (Proof[N] => Proof[N]) with fixNodes {
  
  def globalAxioms: Boolean
  
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence
  
  /**
   * applies the compression algorithm to a proof
   * first it calls the method buildGlobalCongruence with the proof and a newly created equality references object
   * the result is a congruence structure with all input axioms
   * 
   * in the traversal of the proof
   * it first checks its input derived status
   * then it fixes the current node
   * all equations split in right (suc) and left (ant) in the fixed node are filtered out
   * 
   * if the fixed node is input derived and there are equations on both sides 
   * it is checked whether the explanation (the left side) is redundant for some equation of the right side
   * 
   * to do that it adds the left equalities in the (immutable!) congruence structure
   * and then for all right equations it queries an EquationDijkstra object for a shorter explanation
   * 
   * shorter here means to compare the length of the explanation with the number of equations on the left 
   * and the number of axioms that were already resolved away earlier in the subproof
   * i am not 100% sure if this is the right way to compare sizes or if other things should be taken into account
   * 
   * if there is a shorter explanation it is transformed into a proof and the node is replaced with the root of this proof
   * 
   * @param proof to be compressed
   * @res hopefully shorter proof
   */
  def apply(proof: Proof[N]): Proof[N] = {
    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val notOMap = MMap[EqW,EqW]()
    val (con,eqNodesLeft,eqNodesRight) = buildGlobalCongruence(proof)
    println("all references size: " + eqReferences.size)
    val premiseAxiomMap = MMap[N,Set[EqW]]()
    
    def doReplacement(node: N, leftEqs: Seq[EqW], rightEqs: Seq[EqW], axioms: Set[EqW]) = {
        val globalCon = leftEqs.foldLeft(con)({(A,B) => A.addEquality(B)})
//        val localConRes = globalCon.resolveDeducedQueue
//        val globalConRes = globalCon
        val globalConRes = newCon(eqReferences).addAll(leftEqs.toList)
        var tree: Option[EquationPath] = None
        val canBeCompressed = rightEqs.exists(eq => {
          val (l,r) = (eq.l,eq.r)
          val globalConFinal = globalConRes.addNode(l).addNode(r)
          val path = globalConFinal.explain(l,r)
          path match {
            case Some(p) => {
              val newSize = p.originalEqs.size
//              val oldSize = leftEqs.toSet.union(axioms).size
              val oldSize = leftEqs.size
              if (newSize < oldSize) {
                tree = path
//                println("eq1: " + eq + " s: " + node.conclusion.ant.size + " " + oldSize)
                true
              }
              else false
            }
            case None => false
          }
        })
      if (canBeCompressed) {
//        println("x")
        val path = tree.get
        val pathProof =  path.toProof

        /******************************************************
         * here the actual replacement is done
         * if a node is in fact replaced it is also resolved with all the which it can be resolved with
         *****************************************************/
        
        val usedEqs = path.originalEqs
        pathProof match  {
          case Some(proof) => {
            
            val (resNode, axioms) = usedEqs.foldLeft((proof.root,Set[EqW]()))({(A,B) => 
              eqNodesRight.get(B) match {
                case Some(node) => {
                  val x = 
                    try (R(A._1,node))
                    catch {
                      case e: Exception => {
                        println(Proof(A._1))
                        println(Proof(node))
                        println((A._1.conclusion.ant.map(EqW(_).l.t) ++ A._1.conclusion.suc.map(EqW(_).l.t)).mkString(","))
                        println((node.conclusion.ant.map(EqW(_).l.t) ++ node.conclusion.suc.map(EqW(_).l.t)).mkString(","))
                        println(B + "\n" + B.l.t)
                        throw e
                      }
                    }
                  (x, A._2 + EqW(node.conclusion.suc.last))
                }
                case None => {
//                  println("no node for " + B)
                  A
                }
              }
            })
//            println("replacing \n"+node+"with\n"+resNode)
//            if (resNode.conclusion.ant.size > node.conclusion.ant.size) println("compressing, but clause got bigger")
//            println("eq2: " + resNode.conclusion.suc.mkString(","))
            (resNode,axioms)
          }
          case None => {
            println("y" + node)
            println(path)
            (node,axioms)
          }
        }
      }
      else (node,axioms)
    }
    
//    def computePremiseAxioms(node: N, fixedNodeInit: N,fromPremises: Seq[Set[EqW]]) = {
//      premiseAxiomMap.getOrElseUpdate(node, {
//        val premiseAxiomsTmp = fromPremises.foldLeft(Set[EqW]())({(A,B) => A union B})
//        if (node == fixedNodeInit) premiseAxiomsTmp
//        else premiseAxiomsTmp.filter(Proof(fixedNodeInit).nodes.contains(_))
//      })
//    }
    
    def computePremiseAxioms(node: N, fixedNodeInit: N, fromPremises: Seq[Set[EqW]]) = {
      fromPremises.foldLeft(Set[EqW]())({(A,B) => A union B})
    }
    
    /**
     * traversal
     */
    def replaceRedundant(node: N, fromPremises: Seq[(N,Set[EqW],Boolean,Boolean)]): (N,Set[EqW],Boolean,Boolean) = {
      
      val premiseCompressed = if (fromPremises.size > 0) fromPremises.map(_._4).max else false
      val inputDerived = 
        if (node.isInstanceOf[at.logic.skeptik.proof.sequent.lk.Axiom]) true 
        else 
          if (fromPremises.size > 0) fromPremises.map(_._3).max else false
      val premiseNodes = fromPremises.map(_._1)
      
//      println("fixing \n" + node + "with premises\n" + premiseNodes)
      val fixedNodeInit = fixNode(node,premiseNodes)
      
      val premiseAxioms = computePremiseAxioms(node, fixedNodeInit,fromPremises.map(_._2))
      
      val rightEqs = fixedNodeInit.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
      val leftEqs = fixedNodeInit.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
      
//      val found = (rightEqs.exists(_.toString == "(c_2 = c_3)"))
//      if (found) println("(c_2 = c_3) found in fixed node " + fixedNodeInit)
      
      val rS = rightEqs.size
      val lS = leftEqs.size
            
      val (resNode,resAxioms,compressed) = 
        if (rS > 0 && lS > 0 && inputDerived && !premiseCompressed) {
          val x = doReplacement(fixedNodeInit,leftEqs,rightEqs,premiseAxioms)
          val inX = (x._1.conclusion.ant.exists(_.toString == "(c_2 = c_3)")) 
          val inOrig = (fixedNodeInit.conclusion.ant.exists(_.toString == "(c_2 = c_3)"))
          if (inX != inOrig) {
            println("(c_2 = c_3) only in on of:\n"+fixedNodeInit + "\n" + x._1)
          }
          if (fixedNodeInit != x._1) (x._1,x._2,true)
          else (x._1, x._2, false)
        }
        else {
          if (rS == 1 && lS == 0) { // node is an axiom -> add to list
            (fixedNodeInit,premiseAxioms + rightEqs.last,premiseCompressed)
          }
          else (fixedNodeInit,premiseAxioms,premiseCompressed)
        } 
      (resNode,resAxioms,inputDerived,compressed)
    }
    
    // do traversal
    val (newProof, _,_,_) = proof foldDown replaceRedundant
    
//    println(newProof == proof.root)
    
    // Resolve against axioms
    val resProof = newProof.conclusion.suc.foldLeft(newProof)({(A,B) => 
      eqNodesLeft.get(EqW(B)) match { //probably slow
        case Some(node) => {
          R(A,node)
        }
        case None => {
          println("no equality for " + B)
          A
        }
      }
    })

    val outProof = DAGify(resProof)
    if (!outProof.root.conclusion.isEmpty) println("non empty conclusion!")
    outProof
  }
  
  /******************************************************************************************************************
   * gathers all the input equality and inequality axioms (i.e. single equalities on the right and left respectively)
   * adds input equalities to a newly created congruence structure
   * 
   * input (in)equalities are only those for which 
   * no node with a single equality on the right (left) was used to derive this node
   * 
   * @param proof to gather equalities and create congruence structure for
   * @param references equality reference map
   * 
   * @res triple: -congruence structure with input equalities added
   *              -map from EqW objects representing input equalities to the respective proof nodes
   *              -map from EqW objects representing input inequalities to the respective proof nodes
   */
  def buildGlobalCongruence(proof: Proof[N])(implicit eqReferences: MMap[(E,E),EqW]): (Congruence,MMap[EqW,N],MMap[EqW,N]) = {
    var con = newCon(eqReferences)
    val eqNodesLeft = MMap[EqW,N]()
    val eqNodesRight = MMap[EqW,N]()
    
    def buildTraversal(node: N, fromPremises: Seq[(Boolean,Boolean,IMap[(E,E),EqW])]): (Boolean,Boolean,IMap[(E,E),EqW]) = {
      
      val premiseMap = 
        if (fromPremises.isEmpty) IMap[(E,E),EqW]()
        else {
          val maps = fromPremises.map(_._3)
          maps.tail.foldLeft(maps.head)({(A,B) => 
            A ++ B //Slow ???
          })
        }
      
      val rightEqs = node.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
      val leftEqs = node.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
      
//      val found = (rightEqs.exists(_.toString == "(c_2 = c_3)"))
//      if (found) println("(c_2 = c_3) found in original node " + node)
      
      val bothEqs = rightEqs ++ leftEqs
      bothEqs.foreach(eq => {
        val (l,r) = (eq.l,eq.r)
        eqReferences += ((l,r) -> eq)
//        references += ((r,l) -> eq)
      })
      val eqMap = bothEqs.foldLeft(premiseMap)({(A,B) => 
        A.updated((B.l,B.r), B)
      })
      
      val freshLeft = if (fromPremises.size > 0) fromPremises.map(_._1).min else true
      val freshRight = if (fromPremises.size > 0) fromPremises.map(_._2).min else true
      val freshLeftOut = if(true) {
        val singleLeft = node.conclusion.suc.size == 0 && node.conclusion.ant.size == 1 && node.conclusion.ant.forall(EqW.isEq(_))
        if (singleLeft) {
          val eq = EqW(node.conclusion.ant.last)
          eqNodesLeft += (eq -> node)
          false
        }
        else true
      }
      else false
      val freshRightOut = if (freshRight) {
        val singleRight = node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0 && node.conclusion.suc.forall(EqW.isEq(_))
        if (singleRight) {
          val eq = EqW(node.conclusion.suc.last)
          if (globalAxioms) con = con.addEquality(eq)
          eqNodesRight += (eq -> node)
          false
        }
        else true
      }
      else false
      (freshLeftOut,freshRightOut,eqMap)
    }
    val (_,_,mapRes) = proof foldDown buildTraversal
    if (globalAxioms) con = con.resolveDeducedQueue
    (con,eqNodesLeft,eqNodesRight)
  }
}